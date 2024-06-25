//! dfsan logic into targets
//! The colorization stage from `colorization()` in afl++
use alloc::{
    borrow::ToOwned, collections::binary_heap::BinaryHeap, string::{String, ToString}, vec::Vec
};
use core::{cmp::Ordering, fmt::Debug, marker::PhantomData, ops::Range};
use std::collections::HashMap;

use crate::libfuzzer_test_one_input;
use libafl_bolts::{rands::Rand, tuples::{tuple_list, MatchName}, AsSlice};
use serde::{Deserialize, Serialize};

use libafl::{
    corpus::{Corpus, HasCurrentCorpusIdx}, events::{EventFirer, EventRestarter}, executors::{Executor, ExitKind, HasObservers, InProcessExecutor}, inputs::{HasBytesVec, HasTargetBytes}, mark_feature_time, observers::{MapObserver, ObserversTuple}, prelude::{HasClientPerfMonitor, HasExecutions, HasSolutions}, stages::Stage, start_timer, state::{HasCorpus, HasMetadata, HasRand, UsesState}, Error, HasObjective
};

extern crate libc;
use libc::{c_uchar, size_t, c_int};

extern "C" {
    /// keep an array of label values for the conditional following each edge
    pub static mut dfsan_labels_following_edge: [c_uchar; 1024 * 1024];

    /// set the relevant callback(s) for DFSan
    #[link_name = "__dfsan_init.dfsan"]
    fn __dfsan_init();
    /// tag the input with labels 
    #[link_name = "__tag_input_with_labels.dfsan"]
    fn __tag_input_with_labels(
        input: *mut c_uchar, 
        input_len: size_t,
        label_start_offsets: *const size_t, 
        label_block_len: *const size_t, 
        num_labels: c_int
    );
}

pub fn dfsan_init() {
    unsafe { __dfsan_init(); }
}

/// Note this currently execs the program too
pub fn tag_input_with_labels(input: &mut [u8], label_start_offsets: &[usize], label_block_len: &[usize]) {
    unsafe{ 
        __tag_input_with_labels(
            input.as_mut_ptr(), 
            input.len(),
            label_start_offsets.as_ptr(), 
            label_block_len.as_ptr(), 
            label_start_offsets.len() as i32
        ) 
    }
}


// Bigger range is better
#[derive(Debug, PartialEq, Eq)]
struct Bigger(Range<usize>);

impl PartialOrd for Bigger {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bigger {
    fn cmp(&self, other: &Bigger) -> Ordering {
        self.0.len().cmp(&other.0.len())
    }
}

// Earlier range is better
#[derive(Debug, PartialEq, Eq)]
struct Earlier(Range<usize>);

impl PartialOrd for Earlier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Earlier {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.start.cmp(&self.0.start)
    }
}

#[derive(Copy,Clone,Debug)]
struct DFSanLabelInfo {
    label: u8,
    start_pos: usize,
    len: usize
}

/// return a hashmap giving a Vec of labels for each edge
fn run_and_collect_labels<E, EM, Z>(
    fuzzer: &mut Z,
    _executor: &mut E,
    state: &mut E::State,
    manager: &mut EM,
    input: &E::Input,
    labels: &Vec<DFSanLabelInfo>,
) -> Result<HashMap<usize, Vec<u8>>, Error>
where
    E: UsesState,
    EM: EventFirer<State = E::State> + EventRestarter,
    Z: UsesState<State = E::State> + HasObjective,
    E::State: HasCorpus + HasSolutions + HasClientPerfMonitor + HasExecutions,
    E::Input: HasBytesVec,
{
//    let mut harness = |input: &E::Input| {
//        let start_offsets = labels.iter().map(|l| l.start_pos).collect::<Vec<usize>>();
//        let lens = labels.iter().map(|l| l.len).collect::<Vec<usize>>();
//        let mut input_bytes = input.bytes().to_owned();
//        tag_input_with_labels(&mut input_bytes, &start_offsets, &lens);
//
//        unsafe {
//            libfuzzer_test_one_input(&input_bytes);
//        }
//
//        ExitKind::Ok
//    };
//
//    let mut executor =
//        InProcessExecutor::new(&mut harness, tuple_list!(), fuzzer, state, manager)?;
//
//    start_timer!(state);
//    executor.observers_mut().pre_exec_all(state, input)?;
//    mark_feature_time!(state, PerfFeature::PreExecObservers);
//
//    start_timer!(state);
//    let kind = executor.run_target(fuzzer, state, manager, input)?;
//    if kind != ExitKind::Ok {
//        return Err(Error::illegal_state(
//            "Encountered a crash while performing dataflow cmplog.",
//        ));
//    }
//    mark_feature_time!(state, PerfFeature::TargetExecution);

    let start_offsets = labels.iter().map(|l| l.start_pos).collect::<Vec<usize>>();
    let lens = labels.iter().map(|l| l.len).collect::<Vec<usize>>();
    let mut input_bytes = input.bytes().to_owned();
    tag_input_with_labels(&mut input_bytes, &start_offsets, &lens);

    let mut labels_for_edge = HashMap::new();
    unsafe{
        for i in 0..dfsan_labels_following_edge.len() {
            if dfsan_labels_following_edge[i] != 0 {
                let the_byte = dfsan_labels_following_edge[i];
                let mut labels = vec![];
                for bit in 0..8 {
                    if the_byte >> bit & 1 == 1 {
                        labels.push(bit + 1);
                    }
                }
                labels_for_edge.insert(i, labels);
            }
        }
    }

    // start_timer!(state);
    // executor
    //     .observers_mut()
    //     .post_exec_all(state, input, &kind)?;
    // mark_feature_time!(state, PerfFeature::PostExecObservers);

    // *state.executions_mut() += 1;

    Ok(labels_for_edge)
}

/// The mutational stage using power schedules
#[derive(Clone, Debug)]
pub struct DataflowStage<EM, E, Z> {
    #[allow(clippy::type_complexity)]
    phantom: PhantomData<(E, EM, Z)>,
}

impl<EM, E, Z> DataflowStage<EM, E, Z> {
    pub fn new() -> Self {
        dfsan_init();
        DataflowStage { phantom: PhantomData }
    }
}

impl<EM, E, Z> UsesState for DataflowStage<EM, E, Z>
where
    E: UsesState,
{
    type State = E::State;
}

impl<E, EM, Z> Stage<E, EM, Z> for DataflowStage<EM, E, Z>
where
    EM: UsesState<State = E::State> + EventFirer + EventRestarter,
    E: HasObservers + Executor<EM, Z>,
    E::State: HasCorpus + HasMetadata + HasRand + HasExecutions + HasSolutions,
    E::Input: HasBytesVec,
    Z: UsesState<State = E::State> + HasObjective,
{
    type Progress = (); // TODO this stage needs resume

    #[inline]
    #[allow(clippy::let_and_return)]
    fn perform(
        &mut self,
        fuzzer: &mut Z,
        executor: &mut E, // don't need the *main* executor for tracing
        state: &mut E::State,
        manager: &mut EM,
    ) -> Result<(), Error> {
        let idx = state.corpus().current().unwrap();
        let tc = state.corpus().get(idx).unwrap().borrow();
        let input = tc.input().as_ref().unwrap();
        let input_bytes = input.bytes();
        let mut labels = vec![];
        if input_bytes.len() > 7 {
            for idx in 0..8 {
                let start = ((idx as f64) / 8.0 * (input_bytes.len() as f64)).floor() as usize;
                let end = ((idx as f64 + 1f64) / 8f64 * (input_bytes.len() as f64)).floor() as usize;
                labels.push(DFSanLabelInfo { label: idx as u8, start_pos: start, len: end - start });
            }
        } else {
            for idx in 0..input_bytes.len() {
                labels.push(DFSanLabelInfo { label: idx as u8, start_pos: idx, len: 1 });
            }
        }

        let input = input.clone();
        drop(tc);

        let labels_for_edge = run_and_collect_labels(fuzzer, executor, state, manager, &input, &labels)?;

        println!("labels for edge: {:?}", labels_for_edge);

        Ok(())
    }
}

/// Store the taint and the input
#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(
    any(not(feature = "serdeany_autoreg"), miri),
    allow(clippy::unsafe_derive_deserialize)
)] // for SerdeAny
pub struct TaintMetadata {
    input_vec: Vec<u8>,
    ranges: Vec<Range<usize>>,
}

impl TaintMetadata {
    #[must_use]
    /// Constructor for taint metadata
    pub fn new(input_vec: Vec<u8>, ranges: Vec<Range<usize>>) -> Self {
        Self { input_vec, ranges }
    }

    /// Set input and ranges
    pub fn update(&mut self, input: Vec<u8>, ranges: Vec<Range<usize>>) {
        self.input_vec = input;
        self.ranges = ranges;
    }

    #[must_use]
    /// Getter for `input_vec`
    pub fn input_vec(&self) -> &Vec<u8> {
        &self.input_vec
    }

    #[must_use]
    /// Getter for `ranges`
    pub fn ranges(&self) -> &Vec<Range<usize>> {
        &self.ranges
    }
}

libafl_bolts::impl_serdeany!(TaintMetadata);

// impl<EM, O, E, Z> ColorizationStage<EM, O, E, Z>
// where
//     EM: UsesState<State = E::State> + EventFirer,
//     O: MapObserver,
//     E: HasObservers + Executor<EM, Z>,
//     E::State: HasCorpus + HasMetadata + HasRand,
//     E::Input: HasBytesVec,
//     Z: UsesState<State = E::State>,
// {
//     #[inline]
//     #[allow(clippy::let_and_return)]
//     fn locate_tainted_bytes(
//         fuzzer: &mut Z,
//         executor: &mut E,
//         state: &mut E::State,
//         manager: &mut EM,
//         name: &str,
//     ) -> Result<E::Input, Error> {
//         let Some(corpus_idx) = state.current_corpus_idx()? else {
//             return Err(Error::illegal_state(
//                 "state is not currently processing a corpus index",
//             ));
//         };

//         let mut input = state.corpus().cloned_input_for_id(corpus_idx)?;
//         // The backup of the input
//         let backup = input.clone();
//         // This is the buffer we'll randomly mutate during type_replace
//         let mut changed = input.clone();

//         // input will be consumed so clone it
//         let consumed_input = input.clone();

//         // First, run orig_input once and get the original hash

//         // Idea: No need to do this every time
//         let orig_hash =
//             Self::get_raw_map_hash_run(fuzzer, executor, state, manager, consumed_input, name)?;
//         let changed_bytes = changed.bytes_mut();
//         let input_len = changed_bytes.len();

//         // Binary heap, pop is logN, insert is logN
//         // We will separate this range into smaller ranges.
//         // Keep it sorted, we want biggest ones to come first
//         let mut ranges = BinaryHeap::new();
//         ranges.push(Bigger(0..input_len));

//         // This heap contains the smaller ranges. Changes inside them does not affect the coverage.
//         // Keep it sorted, we want the earliest ones to come first so that it's easier to sort them
//         let mut ok_ranges = BinaryHeap::new();

//         // println!("Replaced bytes: {:#?}", changed_bytes);
//         // Now replace with random values (This is type_replace)
//         Self::type_replace(changed_bytes, state);

//         // println!("Replaced bytes: {:#?}", changed_bytes);
//         // What we do is now to separate the input into smaller regions
//         // And in each small regions make sure changing those bytes in the regions does not affect the coverage
//         for _ in 0..input_len * 2 {
//             if let Some(b) = ranges.pop() {
//                 // Let's try the largest one (ranges is sorted)
//                 let r = b.0;
//                 let range_start = r.start;
//                 let range_end = r.end;
//                 let copy_len = r.len();
//                 unsafe {
//                     buffer_copy(
//                         input.bytes_mut(),
//                         changed.bytes(),
//                         range_start,
//                         range_start,
//                         copy_len,
//                     );
//                 }

//                 let consumed_input = input.clone();
//                 let changed_hash = Self::get_raw_map_hash_run(
//                     fuzzer,
//                     executor,
//                     state,
//                     manager,
//                     consumed_input,
//                     name,
//                 )?;

//                 if orig_hash == changed_hash {
//                     // The change in this range is safe!
//                     // println!("this range safe to change: {:#?}", range_start..range_end);

//                     ok_ranges.push(Earlier(range_start..range_end));
//                 } else {
//                     // Seems like this range is too big that we can't keep the original hash anymore

//                     // Revert the changes
//                     unsafe {
//                         buffer_copy(
//                             input.bytes_mut(),
//                             backup.bytes(),
//                             range_start,
//                             range_start,
//                             copy_len,
//                         );
//                     }

//                     // Add smaller range
//                     if copy_len > 1 {
//                         // Separate the ranges
//                         ranges.push(Bigger(range_start..(range_start + copy_len / 2)));
//                         ranges.push(Bigger((range_start + copy_len / 2)..range_end));
//                     }
//                 }
//             } else {
//                 break;
//             }
//         }

//         // Now ok_ranges is a list of smaller range
//         // Each of them should be stored into a metadata and we'll use them later in afl++ redqueen

//         // let's merge ranges in ok_ranges
//         let mut res: Vec<Range<usize>> = Vec::new();
//         for item in ok_ranges.into_sorted_vec().into_iter().rev() {
//             match res.last_mut() {
//                 Some(last) => {
//                     // Try merge
//                     if last.end == item.0.start {
//                         // The last one in `res` is the start of the new one
//                         // so merge
//                         last.end = item.0.end;
//                     } else {
//                         res.push(item.0);
//                     }
//                 }
//                 None => {
//                     res.push(item.0);
//                 }
//             }
//         }

//         if let Some(meta) = state.metadata_map_mut().get_mut::<TaintMetadata>() {
//             meta.update(input.bytes().to_vec(), res);

//             // println!("meta: {:#?}", meta);
//         } else {
//             let meta = TaintMetadata::new(input.bytes().to_vec(), res);
//             state.add_metadata::<TaintMetadata>(meta);
//         }

//         Ok(input)
//     }

//     #[must_use]
//     /// Creates a new [`ColorizationStage`]
//     pub fn new(map_observer_name: &O) -> Self {
//         Self {
//             map_observer_name: map_observer_name.name().to_string(),
//             phantom: PhantomData,
//         }
//     }

//     // Run the target and get map hash but before hitcounts's post_exec is used
//     fn get_raw_map_hash_run(
//         fuzzer: &mut Z,
//         executor: &mut E,
//         state: &mut E::State,
//         manager: &mut EM,
//         input: E::Input,
//         name: &str,
//     ) -> Result<usize, Error> {
//         executor.observers_mut().pre_exec_all(state, &input)?;

//         let exit_kind = executor.run_target(fuzzer, state, manager, &input)?;

//         let observer = executor
//             .observers()
//             .match_name::<O>(name)
//             .ok_or_else(|| Error::key_not_found("MapObserver not found".to_string()))?;

//         let hash = observer.hash() as usize;

//         executor
//             .observers_mut()
//             .post_exec_all(state, &input, &exit_kind)?;

//         // let observers = executor.observers();
//         // fuzzer.process_execution(state, manager, input, observers, &exit_kind, true)?;

//         Ok(hash)
//     }

//     /// Replace bytes with random values but following certain rules
//     #[allow(clippy::needless_range_loop)]
//     fn type_replace(bytes: &mut [u8], state: &mut E::State) {
//         let len = bytes.len();
//         for idx in 0..len {
//             let c = match bytes[idx] {
//                 0x41..=0x46 => {
//                     // 'A' + 1 + rand('F' - 'A')
//                     0x41 + 1 + state.rand_mut().below(5) as u8
//                 }
//                 0x61..=0x66 => {
//                     // 'a' + 1 + rand('f' - 'a')
//                     0x61 + 1 + state.rand_mut().below(5) as u8
//                 }
//                 0x30 => {
//                     // '0' -> '1'
//                     0x31
//                 }
//                 0x31 => {
//                     // '1' -> '0'
//                     0x30
//                 }
//                 0x32..=0x39 => {
//                     // '2' + 1 + rand('9' - '2')
//                     0x32 + 1 + state.rand_mut().below(7) as u8
//                 }
//                 0x47..=0x5a => {
//                     // 'G' + 1 + rand('Z' - 'G')
//                     0x47 + 1 + state.rand_mut().below(19) as u8
//                 }
//                 0x67..=0x7a => {
//                     // 'g' + 1 + rand('z' - 'g')
//                     0x67 + 1 + state.rand_mut().below(19) as u8
//                 }
//                 0x21..=0x2a => {
//                     // '!' + 1 + rand('*' - '!');
//                     0x21 + 1 + state.rand_mut().below(9) as u8
//                 }
//                 0x2c..=0x2e => {
//                     // ',' + 1 + rand('.' - ',')
//                     0x2c + 1 + state.rand_mut().below(2) as u8
//                 }
//                 0x3a..=0x40 => {
//                     // ':' + 1 + rand('@' - ':')
//                     0x3a + 1 + state.rand_mut().below(6) as u8
//                 }
//                 0x5b..=0x60 => {
//                     // '[' + 1 + rand('`' - '[')
//                     0x5b + 1 + state.rand_mut().below(5) as u8
//                 }
//                 0x7b..=0x7e => {
//                     // '{' + 1 + rand('~' - '{')
//                     0x7b + 1 + state.rand_mut().below(3) as u8
//                 }
//                 0x2b => {
//                     // '+' -> '/'
//                     0x2f
//                 }
//                 0x2f => {
//                     // '/' -> '+'
//                     0x2b
//                 }
//                 0x20 => {
//                     // ' ' -> '\t'
//                     0x9
//                 }
//                 0x9 => {
//                     // '\t' -> ' '
//                     0x20
//                 }
//                 0xd => {
//                     // '\r' -> '\n'
//                     0xa
//                 }
//                 0xa => {
//                     // '\n' -> '\r'
//                     0xd
//                 }
//                 0x0 => 0x1,
//                 0x1 | 0xff => 0x0,
//                 _ => {
//                     if bytes[idx] < 32 {
//                         bytes[idx] ^ 0x1f
//                     } else {
//                         bytes[idx] ^ 0x7f
//                     }
//                 }
//             };

//             bytes[idx] = c;
//         }
//     }
// }
