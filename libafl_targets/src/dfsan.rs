//! dfsan logic into targets
//! The colorization stage from `colorization()` in afl++
use alloc::{borrow::ToOwned, vec::Vec};
use core::{fmt::Debug, marker::PhantomData, ops::Range};
use hashbrown::{HashMap, HashSet};
use nix::sys::signal::Signal;
use std::path::PathBuf;

// use crate::libfuzzer_test_one_input;
use libafl_bolts::{
    dataflow_metadata::{
        FuzzerDataflowMetadata, TestcaseDataflowMetadata, TestcaseDirectNeighboursMetadata,
    },
    ownedref::OwnedMutSlice,
    rands::Rand,
    shmem::{ShMemDescription, ShMemMetadata},
    tuples::{tuple_list, tuple_list_type},
    shmem::UnixShMemProvider,
    AsSliceMut, HasLen,
};

use libafl::{
    common::HasMetadata,
    corpus::{Corpus, CorpusId},
    events::{EventFirer, EventRestarter},
    executors::{Executor, HasObservers, ForkserverExecutor},
    feedbacks::{
        cfg_prescience::ControlFlowGraph, MapIndexesMetadata, MapNeighboursFeedbackMetadata,
    },
    inputs::{BytesInput, HasMutatorBytes, HasTargetBytes, UsesInput},
    mark_feature_time,
    mutators::{
        BitFlipMutator, ByteAddMutator, ByteDecMutator, ByteFlipMutator, ByteIncMutator,
        ByteInterestingMutator, ByteNegMutator, ByteRandMutator, BytesCopyMutator,
        BytesRandSetMutator, BytesSetMutator, BytesSwapMutator, DwordAddMutator,
        DwordInterestingMutator, MutationResult, Mutator, QwordAddMutator, StdScheduledMutator,
        WordAddMutator, WordInterestingMutator,
    },
    observers::{hitcount_map::HitcountsMapObserver, map::StdMapObserver, TimeObserver},
    stages::{
        mutational::{MutatedTransform, MutatedTransformPost},
        Stage,
    },
    state::{HasExecutions, HasSolutions},
    start_timer,
    state::{HasCorpus, HasRand, UsesState},
    Error, Evaluator, ExecuteInputResult, HasObjective,
};

#[derive(Copy, Clone, Debug)]
struct DFSanLabelInfo {
    start_pos: usize,
    len: usize,
}

/// Tuple type of the mutations that compose the Havoc mutator
pub type HavocMutationsFixedLengthType = tuple_list_type!(
    BitFlipMutator,
    ByteFlipMutator,
    ByteIncMutator,
    ByteDecMutator,
    ByteNegMutator,
    ByteRandMutator,
    ByteAddMutator,
    WordAddMutator,
    DwordAddMutator,
    QwordAddMutator,
    ByteInterestingMutator,
    WordInterestingMutator,
    DwordInterestingMutator,
    BytesSetMutator,
    BytesRandSetMutator,
    BytesCopyMutator,
    BytesSwapMutator,
);

/// Get the mutations that compose the Havoc mutator (only applied to single inputs)
#[must_use]
pub fn havoc_mutations_fixed_length() -> HavocMutationsFixedLengthType {
    tuple_list!(
        BitFlipMutator::new(),
        ByteFlipMutator::new(),
        ByteIncMutator::new(),
        ByteDecMutator::new(),
        ByteNegMutator::new(),
        ByteRandMutator::new(),
        ByteAddMutator::new(),
        WordAddMutator::new(),
        DwordAddMutator::new(),
        QwordAddMutator::new(),
        ByteInterestingMutator::new(),
        WordInterestingMutator::new(),
        DwordInterestingMutator::new(),
        BytesSetMutator::new(),
        BytesRandSetMutator::new(),
        BytesCopyMutator::new(),
        BytesSwapMutator::new(),
    )
}

/// The mutational stage using power schedules
#[derive(Debug)]
pub struct DataflowStage<'a, EM, E, Z>
where
    E: UsesState,
{
    // mutator: StdScheduledMutator<E::Input, HavocMutationsFixedLengthType, E::State>,
    executor: ForkserverExecutor<
        (
            HitcountsMapObserver<StdMapObserver<'a, u8, false>>,
            (TimeObserver, ()),
        ),
        E::State,
        UnixShMemProvider,
    >,
    dfsan_labels_map: OwnedMutSlice<'a, u8>,
    mutations_per_stage: usize,
    last_new_corpus_entry_time: Option<(CorpusId, std::time::Instant)>,
    #[allow(clippy::type_complexity)]
    phantom: PhantomData<(E, EM, Z)>,
}

impl<'a, EM, E, Z> DataflowStage<'a, EM, E, Z>
where
    E: UsesState + UsesInput,
    E::State: HasRand + HasMetadata + HasCorpus,
    E::Input: HasMutatorBytes + HasTargetBytes,
{
    /// Create a new instance, this includes a forkserver
    pub fn new(
        state: &mut E::State,
        dfsan_binary_path: PathBuf,
        timeout: std::time::Duration,
        map_size: usize,
        cov_map_slice: OwnedMutSlice<'a, u8>,
        dfsan_labels_map_slice: OwnedMutSlice<'a, u8>,
        shmem_provider: &mut UnixShMemProvider,
        input_shmem_desc: Option<ShMemDescription>,
        mutations_per_stage: usize,
    ) -> Self {
        // Create an observation channel using the hitcounts map of AFL++
        let edges_observer = HitcountsMapObserver::new(StdMapObserver::from_ownedref(
            "dfsan_edges_map",
            cov_map_slice,
        ));

        // Create an observation channel to keep track of the execution time
        let time_observer = TimeObserver::new("dfsan_time");

        let mut fs_builder = ForkserverExecutor::builder()
            .program(dfsan_binary_path)
            .shmem_provider(shmem_provider, input_shmem_desc)
            .debug_child(false)
            // .parse_afl_cmdline(arguments)
            .coverage_map_size(map_size)
            .timeout(timeout)
            .kill_signal(Signal::SIGKILL)
            .is_persistent(true);
        let executor = fs_builder
            .build(tuple_list!(edges_observer, time_observer))
            .unwrap();

        if let Ok(shmem_meta) = state.metadata_mut::<ShMemMetadata>() {
            shmem_meta.fserver_input_description = executor.input_shared_mem_description();
        }

        DataflowStage {
            executor,
            dfsan_labels_map: dfsan_labels_map_slice,
            mutations_per_stage,
            last_new_corpus_entry_time: None,
            phantom: PhantomData,
        }
    }

    /// return a hashmap giving a Vec of labels for each edge
    fn run_and_collect_labels(
        &mut self,
        fuzzer: &mut Z,
        _executor: &mut E,
        state: &mut E::State,
        manager: &mut EM,
        input: &E::Input,
        labels: &Vec<DFSanLabelInfo>,
        required_edges: &HashSet<usize>,
    ) -> Result<HashMap<u8, HashSet<usize>>, Error>
    where
        E: UsesState,
        EM: EventFirer<State = E::State> + EventRestarter,
        Z: UsesState<State = E::State> + HasObjective,
        E::State: HasCorpus + HasSolutions + HasExecutions,
        E::Input: HasMutatorBytes,
    {
        let buf = self.dfsan_labels_map.as_slice_mut();
        buf[0] = labels.len() as u8;
        let mut pos = 1;
        for label in labels {
            buf[pos] = ((label.start_pos >> 24) & 0xFF) as u8;
            buf[pos + 1] = ((label.start_pos >> 16) & 0xFF) as u8;
            buf[pos + 2] = ((label.start_pos >> 8) & 0xFF) as u8;
            buf[pos + 3] = (label.start_pos & 0xFF) as u8;
            pos += 4;

            buf[pos] = ((label.len >> 24) & 0xFF) as u8;
            buf[pos + 1] = ((label.len >> 16) & 0xFF) as u8;
            buf[pos + 2] = ((label.len >> 8) & 0xFF) as u8;
            buf[pos + 3] = (label.len & 0xFF) as u8;
            pos += 4;
        }

        self.executor.run_target(fuzzer, state, manager, input).unwrap();

        // let mut all_edges_for_label: HashMap<u8, Vec<usize>> = HashMap::new();
        // for edge_num in 0..31 {
        //         let the_byte = buf[edge_num];
        //         for bit in 0..8 {
        //             if (the_byte >> bit) & 1 == 1 {
        //                 let label_num = bit + 1;
        //                 if let Some(edges) = all_edges_for_label.get_mut(&label_num) {
        //                     edges.push(edge_num);
        //                 } else {
        //                     all_edges_for_label.insert(label_num, vec![edge_num]);
        //                 }
        //             }
        //         }
        // }
        // println!("labels: {:?}, all_edges_for_label: {:?}", labels, all_edges_for_label);

        let mut edges_for_label: HashMap<u8, HashSet<usize>> = HashMap::new();
        for &edge_num in required_edges {
            if buf[edge_num] != 0 {
                let the_byte = buf[edge_num];
                for bit in 0..8 {
                    if (the_byte >> bit) & 1 == 1 {
                        let label_num = bit + 1;
                        if let Some(edges) = edges_for_label.get_mut(&label_num) {
                            edges.insert(edge_num);
                        } else {
                            edges_for_label.insert(label_num, HashSet::from([edge_num]));
                        }
                    }
                }
            }
        }

        Ok(edges_for_label)
    }

    fn get_bytes_depended_on_by_edges(
        &mut self,
        fuzzer: &mut Z,
        executor: &mut E,
        state: &mut E::State,
        manager: &mut EM,
        required_edges: &[usize],
    ) -> Result<HashMap<usize, Vec<usize>>, Error>
    where
        EM: UsesState<State = E::State> + EventFirer + EventRestarter,
        E: HasObservers + Executor<EM, Z>,
        E::State: HasCorpus + HasMetadata + HasRand + HasExecutions + HasSolutions,
        E::Input: HasMutatorBytes,
        Z: UsesState<State = E::State> + HasObjective,
    {
        let input = {
            let idx = state.corpus().current().unwrap();
            let tc = state.corpus().get(idx).unwrap().borrow();
            tc.input().as_ref().unwrap().clone()
        };

        self.executor.run_target(fuzzer, state, manager, &input)?;

        fn get_labels_for_range(range: Range<usize>) -> Vec<DFSanLabelInfo> {
            let mut labels = vec![];
            if range.len() > 8 {
                let mut prev_end = 0usize;
                for idx in 1..9 {
                    let end = (idx as f64 / 8f64 * range.len() as f64).floor() as usize;
                    let len = end - prev_end;
                    labels.push(DFSanLabelInfo {
                        start_pos: range.start + prev_end,
                        len,
                    });
                    prev_end = end;
                }
            } else {
                for idx in 0..range.len() {
                    labels.push(DFSanLabelInfo {
                        start_pos: range.start + idx,
                        len: 1,
                    });
                }
            }
            labels
        }

        let mut bytes_depended_on_by_edge = {
            let mut tmp = HashMap::new();
            for e in required_edges {
                tmp.insert(*e, Vec::with_capacity(20));
            }
            tmp
        };

        let all_required: HashSet<usize> = required_edges.iter().cloned().collect();
        let mut stack = vec![(all_required, 0..input.bytes().len())];
        // once there are 20 bytes dependent, stop trying to compute more!
        let mut saturated_conds = HashSet::new();
        // println!("input len: {:?}", input.bytes().len());

        let mut exec_time = std::time::Duration::new(0, 0);
        let mut filter_req_time = std::time::Duration::new(0, 0);
        let mut populate_dependent = std::time::Duration::new(0, 0);
        let mut execs = 0;
        // Collect up a list of bytes that each edge depends on; these may be disjoint
        // e.g. if (data[0] + data[3] - data[5] == 0)
        while let Some((mut required_edges, byte_range)) = stack.pop() {
            let start = std::time::Instant::now();
            if required_edges.len() < saturated_conds.len() {
                required_edges.retain(|req| !saturated_conds.contains(req));
            } else {
                for sat in &saturated_conds { required_edges.remove(sat); }
            }
            filter_req_time += start.elapsed();
            if required_edges.is_empty() {
                continue;
            }

            let start = std::time::Instant::now();
            let label_infos = get_labels_for_range(byte_range);
            let edges_for_label = self.run_and_collect_labels(
                fuzzer,
                executor,
                state,
                manager,
                &input,
                &label_infos,
                &required_edges,
            )?;
            execs += 1;
            exec_time += start.elapsed();
            let start = std::time::Instant::now();

            // println!("edges_for_label: {:?}", edges_for_label);
            for (label, edges) in edges_for_label {
                let linfo = label_infos[(label as usize) - 1];
                if linfo.len == 1 {
                    for edge_idx in edges {
                        let dependent_bytes = bytes_depended_on_by_edge
                            .get_mut(&edge_idx)
                            .unwrap();
                        if dependent_bytes.len() >= 20 {
                            saturated_conds.insert(edge_idx);
                        } else {
                            dependent_bytes.push(linfo.start_pos);
                        }
                    }
                } else {
                    // println!("queueing edges {:?}, {:?}-{:?}", edges, linfo.start_pos, linfo.start_pos + linfo.len);
                    stack.push((edges, linfo.start_pos..(linfo.start_pos + linfo.len)));
                }
            }

            populate_dependent += start.elapsed();
        }

        for (_edge_idx, bytes) in bytes_depended_on_by_edge.iter_mut() {
            bytes.sort();
            bytes.shrink_to_fit();
        }

        println!(
            "bytes depended on by edge: {:?}",
            bytes_depended_on_by_edge
                .iter()
                .filter(|(_, x)| x.len() > 0)
                .map(|(edge, bytes)| {
                    if bytes.len() > 10 {
                        (edge, format!("{} bytes", bytes.len()))
                    } else {
                        (edge, format!("{:?}", bytes))
                    }
                })
                .collect::<HashMap<&usize, std::string::String>>()
        );

        println!("getting dependencies breakdown, exec time: {:?} ({execs} execs {:?} each), filter reqs: {:?}, populate dependent: {:?}",
            exec_time, exec_time / execs, filter_req_time, populate_dependent);

        // Save memory by filtering large dependencies (chances are the targetting won't help much)
        // bytes_depended_on_by_edge = bytes_depended_on_by_edge
        //     .into_iter()
        //     .filter(|(_edge, bytes)| bytes.len() < 20)
        //     .collect();

        Ok(bytes_depended_on_by_edge)
    }

    fn do_simple_mutate(
        &mut self,
        fuzzer: &mut Z,
        state: &mut E::State,
        executor: &mut E,
        manager: &mut EM,
        num_mutations: usize,
    ) -> Result<(), Error>
    where
        EM: UsesState<State = E::State> + EventFirer + EventRestarter,
        E: HasObservers + Executor<EM, Z>,
        E::State: HasCorpus + HasMetadata + HasRand + HasExecutions + HasSolutions,
        E::Input: HasMutatorBytes + HasTargetBytes,
        Z: UsesState<State = E::State> + HasObjective + Evaluator<E, EM>,
    {
        let idx = state.corpus().current().unwrap();

        let mut mutator =
            StdScheduledMutator::with_max_stack_pow(havoc_mutations_fixed_length(), 6);

        let original_input = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            tc.input().as_ref().unwrap().clone()
        };

        let target_bytes_pos = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            let df_meta = tc.metadata::<TestcaseDataflowMetadata>().unwrap();
            let mut res = HashSet::new();
            for (_edge, bytes) in &df_meta.bytes_depended_on_by_uncovered_bb {
                for byte_pos in bytes {
                    res.insert(*byte_pos);
                }
            }
            res
        };

        // build a vec of the values of target bytes
        let target_bytes = {
            let mut res = Vec::with_capacity(target_bytes_pos.len());
            for &pos in &target_bytes_pos {
                res.push(original_input.bytes()[pos]);
            }
            res
        };

        // println!("For parent {parent} running {num_mutations} mutations on bytes {:?}", target_byte_pos);
        let target_bytes_input = BytesInput::new(target_bytes.clone());

        // test out num_mutations different mutants
        for _ in 0..num_mutations {
            let mut input = target_bytes_input.clone();

            start_timer!(state);
            let mutated = mutator.mutate(state, &mut input)?;
            mark_feature_time!(state, PerfFeature::Mutate);

            if mutated == MutationResult::Skipped {
                continue;
            }

            let altered_bytes = input.bytes().to_vec();
            let mut input = original_input.clone();
            let bytes = input.bytes_mut();
            // replace the target bytes with the mutated byte values
            for (arr_idx, dest_pos) in target_bytes_pos.iter().enumerate() {
                bytes[*dest_pos] = altered_bytes[arr_idx];
            }

            // Time is measured directly the `evaluate_input` function
            let (untransformed, post) = input.try_transform_into(state)?;
            let (result, corpus_idx) =
                fuzzer.evaluate_input(state, executor, manager, untransformed)?;

            if result == ExecuteInputResult::Corpus {
                println!("Dataflow stage found a new corpus entry!");
            }

            start_timer!(state);
            mutator.post_exec(state, corpus_idx)?;
            post.post_exec(state, corpus_idx)?;
            mark_feature_time!(state, PerfFeature::MutatePostExec);
        }

        Ok(())
    }
}

impl<'a, EM, E, Z> UsesState for DataflowStage<'a, EM, E, Z>
where
    E: UsesState + UsesInput,
    E::State: HasRand,
    E::Input: HasMutatorBytes,
{
    type State = E::State;
}

impl<'a, E, EM, Z> Stage<E, EM, Z> for DataflowStage<'a, EM, E, Z>
where
    EM: UsesState<State = E::State> + EventFirer + EventRestarter,
    E: HasObservers + Executor<EM, Z>,
    E::State: HasCorpus + HasMetadata + HasRand + HasExecutions + HasSolutions,
    E::Input: HasMutatorBytes + HasTargetBytes,
    Z: UsesState<State = E::State> + HasObjective + Evaluator<E, EM>,
{
    #[inline]
    #[allow(clippy::let_and_return)]
    fn perform(
        &mut self,
        fuzzer: &mut Z,
        executor: &mut E, // don't need the *main* executor for tracing
        state: &mut E::State,
        manager: &mut EM,
    ) -> Result<(), Error> {
        if state.metadata::<FuzzerDataflowMetadata>().is_err() {
            state.add_metadata(FuzzerDataflowMetadata {
                num_mutations_for_edge: HashMap::new(),
            });
        }

        let last_new = self.last_new_corpus_entry_time;
        if let Some(last) = state.corpus().last() {
            if last_new.is_none() || last > last_new.unwrap().0 {
                self.last_new_corpus_entry_time = Some((last, std::time::Instant::now()));
            }
        }

        // let Some((corpus_id, found_time)) = last_new else {
        //     return Ok(());
        // };

        // if found_time.elapsed() < std::time::Duration::from_secs(3) {
        //     return Ok(());
        // }

        let num_mutations = 1 + state.rand_mut().below(self.mutations_per_stage);

        let full_neighbours_meta = state.metadata::<MapNeighboursFeedbackMetadata>().unwrap();
        let covered_blocks = full_neighbours_meta.covered_blocks.clone();

        let idx = state.corpus().current().unwrap();
        let mut tc = state.corpus().get(idx).unwrap().borrow_mut();

        start_timer!(state);

        // Compute the metadata if not present
        if tc.metadata::<TestcaseDataflowMetadata>().is_err() {
            let start = std::time::Instant::now();
            // let covered_meta = tc.metadata::<MapIndexesMetadata>().unwrap();
            // let covered_indexes = covered_meta.list.clone();

            let siblings_for_covered_bb: HashMap<usize, Vec<usize>> = {
                let siblings_for_covered_bb = &mut tc
                    .metadata_mut::<TestcaseDirectNeighboursMetadata>()
                    .unwrap()
                    .siblings_for_covered_bb;

                // clear out any bbs that are now covered
                siblings_for_covered_bb.retain(|current, siblings| {
                    siblings.retain(|s| !covered_blocks.contains(s));
                    !siblings.is_empty()
                });

                siblings_for_covered_bb.clone()
            };
            drop(tc);
            // let mut sorted_all = covered_blocks.clone().into_iter().collect::<Vec<usize>>();
            // sorted_all.sort();
            // println!("{:?}: covered_indexes: {:?}, direct neighbours: {:?}, all_covered_blocks: {:?}", idx, covered_indexes, direct_neighbours_for_edge, sorted_all);

            // let required_edges: Vec<usize> = covered_indexes; //direct_neighbours_for_edge.keys().copied().collect();
            let required_edges: Vec<usize> = siblings_for_covered_bb.keys().copied().collect();
            let bytes_depended_on_by_bb = self.get_bytes_depended_on_by_edges(
                fuzzer,
                executor,
                state,
                manager,
                &required_edges,
            ).unwrap();

            let mut mutations_tested_on_target_bytes: HashMap<Vec<usize>, usize> = HashMap::new();
            let mut uncovered_bbs_depending_on_bytes: HashMap<Vec<usize>, HashSet<usize>> = HashMap::new();
            let mut bytes_depended_on_by_uncovered_bb = HashMap::new();
            for (edge, bytes) in &bytes_depended_on_by_bb {
                let uncovered_siblings = &siblings_for_covered_bb[edge];
                for sib in uncovered_siblings {
                    bytes_depended_on_by_uncovered_bb.insert(*sib, bytes.clone());
                }
                if let Some(edges) = uncovered_bbs_depending_on_bytes.get_mut(bytes) {
                    for sib in uncovered_siblings { edges.insert(*sib); }
                } else {
                    uncovered_bbs_depending_on_bytes.insert(
                        bytes.to_owned(), HashSet::from_iter(uncovered_siblings.into_iter().cloned())
                    );
                    mutations_tested_on_target_bytes.insert(bytes.to_owned(), 0);
                }
            }


            let meta = TestcaseDataflowMetadata {
                bytes_depended_on_by_uncovered_bb,
                mutations_tested_on_target_bytes,
                uncovered_bbs_depending_on_bytes,
            };
            let mut tc = state.corpus().get(idx).unwrap().borrow_mut();
            tc.add_metadata(meta);
            drop(tc);

            // TODO: We should really keep track of the parents rather than siblings
            //       as there can be many siblings for one parent (eg switch statements)

            // Add any new neighbours to the effort tracker
            let global_meta = state.metadata_mut::<FuzzerDataflowMetadata>().unwrap();
            for siblings in siblings_for_covered_bb.values() {
                for sibling in siblings {
                    if global_meta.num_mutations_for_edge.get(sibling).is_none() {
                        global_meta.num_mutations_for_edge.insert(*sibling, 0);
                    }
                }
            }

        } else {
            drop(tc);
        }
        
        mark_feature_time!(state, PerfFeature::ComputeDataflowDependencies);

        // self.do_simple_mutate(fuzzer, state, executor, manager, num_mutations)?;

        // Filter out any mappings that we no longer need due to basic blocks being discovered
        {
            let mut tc = state.corpus().get(idx).unwrap().borrow_mut();

            let siblings_for_covered_bb = &mut tc
                .metadata_mut::<TestcaseDirectNeighboursMetadata>()
                .unwrap()
                .siblings_for_covered_bb;

            // clear out any bbs that are now covered
            siblings_for_covered_bb.retain(|current, siblings| {
                siblings.retain(|s| !covered_blocks.contains(s));
                !siblings.is_empty()
            });

            let tc_meta = tc.metadata_mut::<TestcaseDataflowMetadata>().unwrap();
            for (bytes, cov_map_idxs) in tc_meta.uncovered_bbs_depending_on_bytes.clone() {
                tc_meta.bytes_depended_on_by_uncovered_bb.retain(|cov_map_idx, _| {
                    !covered_blocks.contains(cov_map_idx)
                });
                tc_meta.uncovered_bbs_depending_on_bytes.retain(|bytes, cov_map_idxs| {
                    cov_map_idxs.retain(|idx| !covered_blocks.contains(idx));
                    !cov_map_idxs.is_empty()
                });
            }
        }

        let tc_meta_copy = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            tc.metadata::<TestcaseDataflowMetadata>().unwrap().clone()
        };
        let siblings_for_covered_bb = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            tc.metadata::<TestcaseDirectNeighboursMetadata>()
                .unwrap()
                .siblings_for_covered_bb
                .clone()
        };
        let df_meta = state.metadata::<FuzzerDataflowMetadata>().unwrap();

        let mut power_for_mutation_target_bytes = HashMap::new();
        let mut total_muts = 0usize;
        let mut max_power = 0usize;

        // recalc which edges we've found corpus entries for (so we don't waste time mutating bytes we don't need to)
        for (current, siblings) in &siblings_for_covered_bb {
            for sibling in siblings {
                let Some(dependent_bytes) = tc_meta_copy.bytes_depended_on_by_uncovered_bb.get(sibling) else {
                    continue;
                };
                if dependent_bytes.is_empty() {
                    continue;
                }
                let muts = tc_meta_copy.mutations_tested_on_target_bytes[dependent_bytes];
                // if we've already tested every possible value for this edge...
                if (dependent_bytes.len() == 1 && muts >= 256)
                    || (dependent_bytes.len() == 2 && muts >= 65536 + 32768)
                {
                    continue;
                }

                let mut power = 0;
                let muts = df_meta.num_mutations_for_edge.get(sibling).unwrap();
                power += muts;

                if let Some(bytes_power) = power_for_mutation_target_bytes.get_mut(dependent_bytes) {
                    *bytes_power += power;
                    if *bytes_power > max_power {
                        max_power = *bytes_power;
                    }
                } else {
                    power_for_mutation_target_bytes.insert(dependent_bytes.to_vec(), power);
                    if power > max_power {
                        max_power = power;
                    }
                }

                total_muts += power;
            }
        }

        // Calculate how much to mutate the bytes for each target edge
        let mutations_for_target_bytes = {
            let mut res = HashMap::new();
            // we haven't fuzzed any of these yet! Fuzz them all the same amount
            if total_muts == 0 {
                let muts =
                    f64::ceil(num_mutations as f64 / power_for_mutation_target_bytes.len() as f64)
                        as usize;

                for (target_bytes, _) in power_for_mutation_target_bytes {
                    res.insert(target_bytes, muts);
                }
            // Assign more mutations to underserviced edges
            } else {
                let required_muts = power_for_mutation_target_bytes.len() * max_power - total_muts;
                // we can catch all up to the same number of mutations
                if required_muts < num_mutations {
                    let mut available_muts = num_mutations;
                    // make sure that all edges catch up to the same value
                    for (target_bytes, muts) in &power_for_mutation_target_bytes {
                        available_muts -= max_power - *muts;
                        res.insert(target_bytes.to_owned(), max_power - *muts);
                    }

                    // distribute the remaining mutations fairly
                    let power = f64::ceil(
                        available_muts as f64 / power_for_mutation_target_bytes.len() as f64,
                    ) as usize;

                    for (_target_bytes, muts) in res.iter_mut() {
                        *muts += power;
                    }
                } else {
                    // best effort to even out mutations
                    for (target_bytes, muts) in power_for_mutation_target_bytes {
                        // figure out how far this edge is behind proportionally
                        let to_perform = f64::ceil(
                            ((max_power - muts) as f64 / required_muts as f64)
                                * num_mutations as f64,
                        ) as usize;

                        if to_perform > 0 {
                            res.insert(target_bytes, to_perform);
                        }
                    }
                }
            }
            res
        };

        let mut mutator =
            StdScheduledMutator::with_max_stack_pow(havoc_mutations_fixed_length(), 6);

        let original_input = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            tc.input().as_ref().unwrap().clone()
        };

        // iterate through all of the edges with uncovered neighbours and test out
        // num_mutations different mutants
        for (target_bytes_pos, num_mutations) in &mutations_for_target_bytes {
            if target_bytes_pos.is_empty() {
                continue;
            }

            // build a vec of the values of target bytes
            let target_bytes = {
                let mut res = Vec::with_capacity(target_bytes_pos.len());
                for &pos in target_bytes_pos {
                    res.push(original_input.bytes()[pos]);
                }
                res
            };

            // println!("For parent {parent} running {num_mutations} mutations on bytes {:?}", target_byte_pos);
            let target_bytes_input = BytesInput::new(target_bytes.clone());

            // test out num_mutations different mutants
            for _ in 0..*num_mutations {
                let mut input = target_bytes_input.clone();

                start_timer!(state);
                let altered_bytes = if input.bytes().len() >= 3 {
                    // There are a few bytes to mutate here, use the mutator
                    let mutated = mutator.mutate(state, &mut input).unwrap();

                    if mutated == MutationResult::Skipped {
                        continue;
                    }

                    input.bytes()
                } else {
                    // There are 1 or 2 bytes here - we can do an exhaustive search
                    let bytes = input.bytes_mut();

                    let mut tc = state.corpus_mut().get(idx).unwrap().borrow_mut();
                    let tc_meta = tc.metadata_mut::<TestcaseDataflowMetadata>().unwrap();
                    let tested_vals = tc_meta
                        .mutations_tested_on_target_bytes
                        .get_mut(target_bytes_pos)
                        .unwrap();
                    if (bytes.len() == 1 && *tested_vals >= 256)
                        || (bytes.len() == 2 && *tested_vals >= 65536 + 32768)
                    {
                        println!(
                            "Dataflow Finished all possible combos for {:?} ({tested_vals})",
                            *target_bytes_pos
                        );
                        // We've tested all combinations - bail
                        break;
                    }

                    if bytes.len() == 1 {
                        bytes[0] = *tested_vals as u8;
                    } else if bytes.len() == 2 {
                        let array = if *tested_vals >= 65536 {
                            // done alternating endianness, just whip through the rest BE
                            ((*tested_vals - 32768) as u16).to_be_bytes()
                        } else if *tested_vals % 2 == 0 {
                            // test the next big-endian value
                            ((*tested_vals / 2) as u16).to_be_bytes()
                        } else {
                            // test the next little-endian value
                            ((*tested_vals / 2) as u16).to_le_bytes()
                        };

                        bytes[0] = array[0];
                        bytes[1] = array[1];
                    } else {
                        panic!("Not implemented!")
                    }
                    *tested_vals += 1;

                    input.bytes()
                };
                mark_feature_time!(state, PerfFeature::Mutate);

                let mut input = original_input.clone();
                let bytes = input.bytes_mut();
                // replace the target bytes with the mutated byte values
                for (arr_idx, dest_pos) in target_bytes_pos.iter().enumerate() {
                    bytes[*dest_pos] = altered_bytes[arr_idx];
                }

                // Time is measured directly the `evaluate_input` function
                let (untransformed, post) = input.try_transform_into(state).unwrap();
                start_timer!(state);
                let (result, corpus_idx) =
                    fuzzer.evaluate_input(state, executor, manager, untransformed).unwrap();
                mark_feature_time!(state, PerfFeature::TargetExecution);

                if result == ExecuteInputResult::Corpus {
                    println!(
                        "Dataflow stage found a new corpus entry! (through exhaustive testing: {})",
                        target_bytes_input.len() < 3
                    );
                }

                start_timer!(state);
                mutator.post_exec(state, corpus_idx).unwrap();
                post.post_exec(state, corpus_idx).unwrap();
                mark_feature_time!(state, PerfFeature::MutatePostExec);
            }
        }

        {
            // update the mutation counts for all the targets
            let df_meta = state.metadata_mut::<FuzzerDataflowMetadata>().unwrap();
            for (target_bytes_pos, num_mutations) in &mutations_for_target_bytes {
                let bbs = &tc_meta_copy.uncovered_bbs_depending_on_bytes[target_bytes_pos];
                for bb_cov_map_idx in bbs {
                    let count = df_meta.num_mutations_for_edge.get_mut(bb_cov_map_idx).unwrap();
                    *count += *num_mutations;
                }
            }
        }

        #[cfg(feature = "introspection")]
        state.introspection_monitor_mut().finish_stage();

        Ok(())
    }

    fn restart_progress_should_run(
        &mut self,
        _: &mut <Self as UsesState>::State,
    ) -> Result<bool, Error> {
        Ok(true)
    }

    fn clear_restart_progress(&mut self, _: &mut <Self as UsesState>::State) -> Result<(), Error> {
        Ok(())
    }
}
