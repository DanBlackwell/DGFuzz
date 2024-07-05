//! A singlethreaded libfuzzer-like fuzzer that can auto-restart.
use mimalloc::MiMalloc;
#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

use core::{cell::RefCell, time::Duration};
#[cfg(unix)]
use std::os::unix::io::{AsRawFd, FromRawFd};
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::PathBuf,
    process,
    ffi::c_int
};

use clap::{Arg, Command};
use libafl::{
    corpus::{Corpus, InMemoryOnDiskCorpus, OnDiskCorpus},
    events::{SimpleEventManager, SimpleRestartingEventManager},
    executors::{inprocess::InProcessExecutor, ExitKind, forkserver::ForkserverExecutor},
    feedback_or,
    feedbacks::{CrashFeedback, MaxMapFeedback, TimeFeedback, cfg_prescience::ControlFlowGraph},
    fuzzer::{Fuzzer, StdFuzzer},
    inputs::{BytesInput, HasTargetBytes},
    monitors::SimpleMonitor,
    mutators::{
        scheduled::havoc_mutations, token_mutations::I2SRandReplace, tokens_mutations,
        StdMOptMutator, StdScheduledMutator, Tokens,
    },
    observers::{StdMapObserver, HitcountsMapObserver, TimeObserver},
    prelude::probabilistic_sampling::UncoveredNeighboursProbabilitySamplingScheduler,
    schedulers::{
        powersched::PowerSchedule, IndexesLenTimeMinimizerScheduler, StdWeightedScheduler,
    },
    stages::{
        calibrate::CalibrationStage, power::StdPowerMutationalStage, StdMutationalStage,
        TracingStage,
    },
    state::{HasCorpus, HasMetadata, StdState},
    Error,
};
use libafl_bolts::{
    current_nanos, current_time,
    os::dup2,
    prelude::OwnedMutSlice,
    rands::StdRand,
    shmem::{ShMemProvider, StdShMemProvider, ShMem},
    tuples::{tuple_list, Merge},
    AsSlice,
    AsMutSlice
};
#[cfg(any(target_os = "linux", target_vendor = "apple"))]
use libafl_targets::autotokens;
use libafl_targets::{
    libfuzzer_initialize, libfuzzer_test_one_input, std_edges_map_observer, CmpLogObserver,
    neighbours_map_mut_slice,
    dfsan::DataflowStage,
};
#[cfg(unix)]
use nix::{self, unistd::dup};

#[allow(non_snake_case)]
extern "C" {
    fn LLVMFuzzerTestOneInput(data: *const u8, len: usize) -> c_int;
}

/// The fuzzer main (as `no_mangle` C function)
#[no_mangle]
pub extern "C" fn libafl_main() {
    // Registry the metadata types used in this fuzzer
    // Needed only on no_std
    // unsafe { RegistryBuilder::register::<Tokens>(); }

    let res = match Command::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author("AFLplusplus team")
        .about("LibAFL-based fuzzer for Fuzzbench")
        .arg(
            Arg::new("out")
                .short('o')
                .long("output")
                .help("The directory to place finds in ('corpus')"),
        )
        .arg(
            Arg::new("in")
                .short('i')
                .long("input")
                .help("The directory to read initial inputs from ('seeds')"),
        )
        .arg(
            Arg::new("tokens")
                .short('x')
                .long("tokens")
                .help("A file to read tokens from, to be used during fuzzing"),
        )
        .arg(
            Arg::new("cfg_file")
                .short('c')
                .long("cfg_file")
                .help("The file to read Control Flow Graph from"),
        )
        .arg(
            Arg::new("dfsan_binary")
                .short('d')
                .long("dfsan_binary")
                .help("Path of the executable compiled with DFSan")
        )
        .arg(
            Arg::new("logfile")
                .short('l')
                .long("logfile")
                .help("Duplicates all output to this file")
                .default_value("libafl.log"),
        )
        .arg(
            Arg::new("timeout")
                .short('t')
                .long("timeout")
                .help("Timeout for each individual execution, in milliseconds")
                .default_value("1200"),
        )
        .arg(Arg::new("remaining"))
        .try_get_matches()
    {
        Ok(res) => res,
        Err(err) => {
            println!(
                "Syntax: {}, [-x dictionary] -o corpus_dir -i seed_dir\n{:?}",
                env::current_exe()
                    .unwrap_or_else(|_| "fuzzer".into())
                    .to_string_lossy(),
                err,
            );
            return;
        }
    };

    println!(
        "Workdir: {:?}",
        env::current_dir().unwrap().to_string_lossy().to_string()
    );

    if let Some(filenames) = res.get_many::<String>("remaining") {
        let filenames: Vec<&str> = filenames.map(String::as_str).collect();
        if !filenames.is_empty() {
            run_testcases(&filenames);
            return;
        }
    }

    // For fuzzbench, crashes and finds are inside the same `corpus` directory, in the "queue" and "crashes" subdir.
    let mut out_dir = PathBuf::from(
        res.get_one::<String>("out")
            .expect("The --output parameter is missing")
            .to_string(),
    );
    if fs::create_dir(&out_dir).is_err() {
        println!("Out dir at {:?} already exists.", &out_dir);
        if !out_dir.is_dir() {
            println!("Out dir at {:?} is not a valid directory!", &out_dir);
            return;
        }
    }
    let mut crashes = out_dir.clone();
    crashes.push("crashes");
    out_dir.push("queue");

    let in_dir = PathBuf::from(
        res.get_one::<String>("in")
            .expect("The --input parameter is missing")
            .to_string(),
    );
    if !in_dir.is_dir() {
        println!("In dir at {:?} is not a valid directory!", &in_dir);
        return;
    }

    let tokens = res.get_one::<String>("tokens").map(PathBuf::from);

    let cfg_file = res.get_one::<String>("cfg_file").map(PathBuf::from);

    let logfile = PathBuf::from(res.get_one::<String>("logfile").unwrap().to_string());

    let dfsan_binary = PathBuf::from(
        res.get_one::<String>("dfsan_binary").unwrap().to_string()
    );

    let timeout = Duration::from_millis(
        res.get_one::<String>("timeout")
            .unwrap()
            .to_string()
            .parse()
            .expect("Could not parse timeout in milliseconds"),
    );

    fuzz(out_dir, crashes, &in_dir, tokens, cfg_file, &logfile, timeout, dfsan_binary)
        .expect("An error occurred while fuzzing");
}

fn run_testcases(filenames: &[&str]) {
    // The actual target run starts here.
    // Call LLVMFUzzerInitialize() if present.
    let args: Vec<String> = env::args().collect();
    if libfuzzer_initialize(&args) == -1 {
        println!("Warning: LLVMFuzzerInitialize failed with -1");
    }

    println!(
        "You are not fuzzing, just executing {} testcases",
        filenames.len()
    );
    for fname in filenames {
        println!("Executing {fname}");

        let mut file = File::open(fname).expect("No file found");
        let mut buffer = vec![];
        file.read_to_end(&mut buffer).expect("Buffer overflow");

        libfuzzer_test_one_input(&buffer);
    }
}

/// The actual fuzzer
#[allow(clippy::too_many_lines)]
fn fuzz(
    corpus_dir: PathBuf,
    objective_dir: PathBuf,
    seed_dir: &PathBuf,
    tokenfile: Option<PathBuf>,
    cfg_file: Option<PathBuf>,
    logfile: &PathBuf,
    timeout: Duration,
    dfsan_binary: PathBuf,
) -> Result<(), Error> {
    let log = RefCell::new(OpenOptions::new().append(true).create(true).open(logfile)?);

    #[cfg(unix)]
    let mut stdout_cpy = unsafe {
        let new_fd = dup(io::stdout().as_raw_fd())?;
        File::from_raw_fd(new_fd)
    };
    #[cfg(unix)]
    let file_null = File::open("/dev/null")?;

    // 'While the monitor are state, they are usually used in the broker - which is likely never restarted
    let monitor = SimpleMonitor::with_user_monitor(|s| {
        #[cfg(unix)]
        writeln!(&mut stdout_cpy, "{s}").unwrap();
        #[cfg(windows)]
        println!("{s}");
        writeln!(log.borrow_mut(), "{:?} {s}", current_time()).unwrap();
    }, true);

    // We need a shared map to store our state before a crash.
    // This way, we are able to continue fuzzing afterwards.
    let mut shmem_provider = StdShMemProvider::new()?;

    let mut mgr = SimpleEventManager::new(monitor);
    let state = None;
    // let (state, mut mgr) = match SimpleRestartingEventManager::launch(monitor, &mut shmem_provider)
    // {
    //     // The restarting state will spawn the same process again as child, then restarted it each time it crashes.
    //     Ok(res) => res,
    //     Err(err) => match err {
    //         Error::ShuttingDown => {
    //             return Ok(());
    //         }
    //         _ => {
    //             panic!("Failed to setup the restarter: {err}");
    //         }
    //     },
    // };

    // Create an observation channel using the coverage map
    // We don't use the hitcounts (see the Cargo.toml, we use pcguard_edges)
    let edges_observer = HitcountsMapObserver::new(unsafe { std_edges_map_observer("edges") });

    // Create an observation channel to keep track of the execution time
    let time_observer = TimeObserver::new("time");

    let cmplog_observer = CmpLogObserver::new("cmplog", true);

    let map_feedback = MaxMapFeedback::tracking(&edges_observer, true, true);

    let calibration = CalibrationStage::new(&map_feedback);

    // Feedback to rate the interestingness of an input
    // This one is composed by two Feedbacks in OR
    let mut feedback = feedback_or!(
        // New maximization map feedback linked to the edges observer and the feedback state
        map_feedback,
        // Time feedback, this one does not need a feedback state
        TimeFeedback::with_observer(&time_observer)
    );

    // A feedback to choose if an input is a solution or not
    let mut objective = CrashFeedback::new();

    // If not restarting, create a State from scratch
    let mut state = state.unwrap_or_else(|| {
        StdState::new(
            // RNG
            StdRand::with_seed(current_nanos()),
            // Corpus that will be evolved, we keep it in memory for performance
            InMemoryOnDiskCorpus::new(corpus_dir).unwrap(),
            // Corpus in which we store solutions (crashes in this example),
            // on disk so the user can get them after stopping the fuzzer
            OnDiskCorpus::new(objective_dir).unwrap(),
            // States of the feedbacks.
            // The feedbacks can report the data that should persist in the State.
            &mut feedback,
            // Same for objective feedbacks
            &mut objective,
        )
        .unwrap()
    });

    println!("Let's fuzz :)");

    // The actual target run starts here.
    // Call LLVMFUzzerInitialize() if present.
    let args: Vec<String> = env::args().collect();
    if libfuzzer_initialize(&args) == -1 {
        println!("Warning: LLVMFuzzerInitialize failed with -1");
    }

    // Setup a randomic Input2State stage
    let i2s = StdMutationalStage::new(StdScheduledMutator::new(tuple_list!(I2SRandReplace::new())));

    // Setup a MOPT mutator
    let mutator = StdMOptMutator::new(
        &mut state,
        havoc_mutations().merge(tokens_mutations()),
        7,
        5,
    )?;

    // let power = StdPowerMutationalStage::new(mutator);
    let mutation = StdMutationalStage::with_max_iterations(mutator, 1024);

    // A minimization+queue policy to get testcasess from the corpus
    // let scheduler = IndexesLenTimeMinimizerScheduler::new(StdWeightedScheduler::with_schedule(
    //     &mut state,
    //     &edges_observer,
    //     Some(PowerSchedule::FAST),
    // ));
    let scheduler = UncoveredNeighboursProbabilitySamplingScheduler::new();

    // A fuzzer with feedbacks and a corpus scheduler
    let mut fuzzer = StdFuzzer::new(scheduler, feedback, objective);

    // The wrapped harness function, calling out to the LLVM-style harness
    let mut harness = |input: &BytesInput| {
        let target = input.target_bytes();
        let buf = target.as_slice();

        unsafe{
            LLVMFuzzerTestOneInput(buf.as_ptr(), buf.len());
        }
        // libfuzzer_test_one_input(buf);
        ExitKind::Ok
    };

    let mut tracing_harness = harness;

    // Create the executor for an in-process function with one observer for edge coverage and one for the execution time
    let mut executor = InProcessExecutor::with_timeout(
        &mut harness,
        tuple_list!(edges_observer, time_observer),
        &mut fuzzer,
        &mut state,
        &mut mgr,
        timeout,
    )?;

    // Setup a tracing stage in which we log comparisons
    let tracing = TracingStage::new(
        InProcessExecutor::with_timeout(
            &mut tracing_harness,
            tuple_list!(cmplog_observer),
            &mut fuzzer,
            &mut state,
            &mut mgr,
            timeout * 10,
        )?,
        // Give it more time!
    );

    // a large initial map size that should be enough
    // to house all potential coverage maps for our targets
    // (we will eventually reduce the used size according to the actual map)
    const MAP_SIZE: usize = 2_621_440 / 2;
    // The coverage map shared between observer and executor
    let mut fs_shmem = shmem_provider.new_shmem(2 * MAP_SIZE).unwrap();

    // let the forkserver know the shmid
    fs_shmem.write_to_env("__AFL_SHM_ID").unwrap();

    let (cov_map_slice, dfsan_labels_slice) = {
        let shmem_buf = fs_shmem.as_mut_ptr_of::<u8>().unwrap();
        unsafe {
            (
              OwnedMutSlice::from_raw_parts_mut(shmem_buf, MAP_SIZE),
              OwnedMutSlice::from_raw_parts_mut(shmem_buf.offset(MAP_SIZE as isize), MAP_SIZE),
            )
        }
    };

    // To let know the AFL++ binary that we have a big map
    std::env::set_var("AFL_MAP_SIZE", format!("{}", MAP_SIZE));
   
    // println!("map_ptr: {:?}, labels: {:?}", map_ptr, dfsan_labels_map_ptr);

    let dataflow = DataflowStage::new(dfsan_binary, timeout, MAP_SIZE, cov_map_slice, dfsan_labels_slice, &mut shmem_provider);

    // The order of the stages matter!
    let mut stages = tuple_list!(calibration, dataflow, tracing, i2s, mutation);

    // Read tokens
    if state.metadata_map().get::<Tokens>().is_none() {
        let mut toks = Tokens::default();
        if let Some(tokenfile) = tokenfile {
            toks.add_from_file(tokenfile)?;
        }
        #[cfg(any(target_os = "linux", target_vendor = "apple"))]
        {
            toks += autotokens()?;
        }

        if !toks.is_empty() {
            state.add_metadata(toks);
        }
    }

    if state.metadata_map().get::<ControlFlowGraph>().is_none() {
        if let Some(cfg_file) = cfg_file {
            let mut control_flow_graph = ControlFlowGraph::new();
            println!("Loading CFG from file: {:?}", cfg_file);
            let mut file = std::fs::File::open(cfg_file)?;
            let mut buffer = Vec::new();
            use std::io::Read;
            file.read_to_end(&mut buffer)?;
            control_flow_graph.parse_from_buf(&buffer);

            let (bb_str, funcs_str) = control_flow_graph.to_graphviz_dot();
            use std::fs::File;
            use std::io::prelude::*;
            let mut file = File::create("bbs.dot").unwrap();
            file.write_all(bb_str.as_bytes()).unwrap();

            file = File::create("funcs.dot").unwrap();
            file.write_all(funcs_str.as_bytes()).unwrap();

            state.add_metadata(control_flow_graph);
        } 
    }

    // In case the corpus is empty (on first run), reset
    if state.must_load_initial_inputs() {
        state
            .load_initial_inputs(&mut fuzzer, &mut executor, &mut mgr, &[seed_dir.clone()])
            .unwrap_or_else(|_| {
                println!("Failed to load initial corpus at {:?}", &seed_dir);
                process::exit(0);
            });
        println!("We imported {} inputs from disk.", state.corpus().count());
    }

    // Remove target output (logs still survive)
    #[cfg(unix)]
    {
        // let null_fd = file_null.as_raw_fd();
        // dup2(null_fd, io::stdout().as_raw_fd())?;
        // if std::env::var("LIBAFL_FUZZBENCH_DEBUG").is_err() {
        //     dup2(null_fd, io::stderr().as_raw_fd())?;
        // }
    }
    // reopen file to make sure we're at the end
    log.replace(OpenOptions::new().append(true).create(true).open(logfile)?);

    fuzzer.fuzz_loop(&mut stages, &mut executor, &mut state, &mut mgr)?;

    // Never reached
    Ok(())
}
