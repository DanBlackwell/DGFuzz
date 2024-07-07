//! dfsan logic into targets
//! The colorization stage from `colorization()` in afl++
use alloc::{
    borrow::ToOwned, collections::binary_heap::BinaryHeap, string::{String, ToString}, vec::Vec
};
use core::{cmp::Ordering, fmt::Debug, marker::PhantomData, ops::Range, slice};
use hashbrown::{HashMap, HashSet};
use std::path::PathBuf;
use nix::sys::signal::Signal;


// use crate::libfuzzer_test_one_input;
use libafl_bolts::{
    rands::Rand, 
    tuples::{tuple_list, tuple_list_type, MatchName}, 
    AsSlice, 
    AsSliceMut,
    prelude::{OwnedMutSlice, ShMemProvider, UnixShMemProvider},
    shmem::ShMem,
};
use serde::{Deserialize, Serialize};

use libafl::{
    common::HasMetadata,
    corpus::{Corpus, HasCurrentCorpusId}, 
    events::{EventFirer, EventRestarter}, 
    executors::{Executor, ExitKind, HasObservers, InProcessExecutor}, 
    feedbacks::{cfg_prescience::ControlFlowGraph, MapIndexesMetadata, MapNeighboursFeedbackMetadata}, 
    inputs::{BytesInput, HasMutatorBytes, HasTargetBytes, UsesInput}, 
    mark_feature_time, 
    mutators::{BitFlipMutator, ByteAddMutator, ByteDecMutator, ByteFlipMutator, ByteIncMutator, ByteInterestingMutator, ByteNegMutator, ByteRandMutator, BytesCopyMutator, BytesRandSetMutator, BytesSetMutator, BytesSwapMutator, DwordAddMutator, DwordInterestingMutator, MutationResult, Mutator, QwordAddMutator, StdScheduledMutator, WordAddMutator, WordInterestingMutator}, 
    observers::{MapObserver, ObserversTuple}, 
    prelude::{HasExecutions, HasSolutions, HitcountsMapObserver, StdMapObserver, TimeObserver, ForkserverExecutor, }, 
    stages::{mutational::{MutatedTransform, MutatedTransformPost}, Stage}, 
    start_timer, 
    state::{HasCorpus, HasRand, UsesState}, 
    Error, 
    Evaluator, 
    ExecuteInputResult,
    HasObjective
};

use libc;
use libc::{c_uchar, size_t, c_int};

#[derive(Clone,Debug,Serialize,Deserialize)]
struct TestcaseDataflowMetadata {
    pub direct_neighbours_for_edge: HashMap<usize, Vec<usize>>,
    /// Map from edge index to bytes that the conditional afterwards depends on
    pub bytes_depended_on_by_edge: HashMap<usize, Vec<usize>>
}

libafl_bolts::impl_serdeany!(TestcaseDataflowMetadata);

#[derive(Copy,Clone,Debug)]
struct DFSanLabelInfo {
    label: u8,
    start_pos: usize,
    len: usize
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
    executor: ForkserverExecutor<(HitcountsMapObserver<StdMapObserver<'a, u8, false>>, (TimeObserver, ())), E::State, UnixShMemProvider>,
    dfsan_labels_map: OwnedMutSlice<'a, u8>,
    #[allow(clippy::type_complexity)]
    phantom: PhantomData<(E, EM, Z)>,
}

impl<'a, EM, E, Z> DataflowStage<'a, EM, E, Z>
where 
    E: UsesState + UsesInput, 
    E::State: HasRand, 
    E::Input: HasMutatorBytes + HasTargetBytes,
{
    pub fn new(
        dfsan_binary_path: PathBuf, 
        timeout: std::time::Duration,
        map_size: usize,
        cov_map_slice: OwnedMutSlice<'a, u8>,
        dfsan_labels_map_slice: OwnedMutSlice<'a, u8>,
        shmem_provider: &mut UnixShMemProvider,
    ) -> Self {

        // Create an observation channel using the hitcounts map of AFL++
        let edges_observer =
            unsafe { HitcountsMapObserver::new(StdMapObserver::from_ownedref("edges_map", cov_map_slice)) };

        // Create an observation channel to keep track of the execution time
        let time_observer = TimeObserver::new("time");
    
        let mut fs_builder = ForkserverExecutor::builder()
            .program(dfsan_binary_path)
            .shmem_provider(shmem_provider)
            .debug_child(true)
            // .parse_afl_cmdline(arguments)
            .coverage_map_size(map_size)
            .timeout(timeout)
            .kill_signal(Signal::SIGKILL)
            .is_persistent(true);
        let mut executor = fs_builder
            .build(tuple_list!(edges_observer, time_observer))
            .unwrap();

        // let dataflow = DataflowStage::new(fs_executor, dfsan_labels_map);
        DataflowStage { executor, dfsan_labels_map: dfsan_labels_map_slice, phantom: PhantomData }
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
        required_edges: &[usize],
    ) -> Result<HashMap<usize, Vec<u8>>, Error>
    where
        E: UsesState,
        EM: EventFirer<State = E::State> + EventRestarter,
        Z: UsesState<State = E::State> + HasObjective,
        E::State: HasCorpus + HasSolutions + HasExecutions,
        E::Input: HasMutatorBytes,
    {
        // println!("tagging input with labels(len: {} {:?}, {:?})", input.bytes().len(), input.bytes(), labels);
        let mut label_num = 1;
        // println!("trying to get the map");
        // println!("{:?}", self.dfsan_labels_map);
        let buf = self.dfsan_labels_map.as_slice_mut();
        unsafe {
            buf[0] = labels.len() as u8;
            let mut pos = 1;
            for label in labels {
                buf[pos]   = ((label.start_pos >> 24) & 0xFF) as u8;
                buf[pos+1] = ((label.start_pos >> 16) & 0xFF) as u8;
                buf[pos+2] = ((label.start_pos >> 8)  & 0xFF) as u8;
                buf[pos+3] = (label.start_pos & 0xFF) as u8;
                pos += 4;

                buf[pos]   = ((label.len >> 24) & 0xFF) as u8;
                buf[pos+1] = ((label.len >> 16) & 0xFF) as u8;
                buf[pos+2] = ((label.len >> 8)  & 0xFF) as u8;
                buf[pos+3] = (label.len & 0xFF) as u8;
                pos += 4;
            }
        }

        self.executor.run_target(fuzzer, state, manager, input)?;

        let mut labels_for_edge = HashMap::new();
        unsafe {
            for &edge_num in required_edges {
                if buf[edge_num] != 0 {
                    let the_byte = buf[edge_num];
                    let mut labels = vec![];
                    for bit in 0..8 {
                        if (the_byte >> bit) & 1 == 1 {
                            labels.push(bit + 1);
                        }
                    }
                    labels_for_edge.insert(edge_num, labels);
                    buf[edge_num] = 0;
                }
            }
        }

        Ok(labels_for_edge)
    }

    fn get_bytes_depended_on_by_edges(
        &mut self,
        fuzzer: &mut Z,
        executor: &mut E,
        state: &mut E::State,
        manager: &mut EM,
        required_edges: &[usize]
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
    
        fn get_labels_for_range(range: Range<usize>) -> Vec<DFSanLabelInfo> {
            let mut labels = vec![];
            if range.len() > 7 {
                for idx in 0..8 {
                    let start_offset = ((idx as f64) / 8f64 * (range.len() as f64)).floor() as usize;
                    let end_offset = ((idx as f64 + 1f64) / 8f64 * (range.len() as f64)).floor() as usize;
                    let len = end_offset - start_offset;
                    labels.push(DFSanLabelInfo { label: idx as u8, start_pos: range.start + start_offset, len });
                }
            } else {
                for idx in 0..range.len() {
                    labels.push(DFSanLabelInfo { label: idx as u8, start_pos: range.start + idx, len: 1 });
                }
            }
            labels
        }
    
        let mut bytes_depended_on_by_edge = {
            let mut tmp = HashMap::new();
            for e in required_edges { tmp.insert(*e, vec![]); }
            tmp
        };
    
        let mut queue = required_edges.iter()
            .map(|&e| (e, 0..input.bytes().len()))
            .collect::<Vec<(usize, Range<usize>)>>();
    
        // Collect up a list of bytes that each edge depends on; these may be disjoint 
        // e.g. if (data[0] + data[3] - data[5] == 0)
        while let Some((edge_idx, byte_range)) = queue.pop() {
            let label_infos = get_labels_for_range(byte_range);
            let labels_for_edge = self.run_and_collect_labels(
                fuzzer, executor, state, manager, &input, &label_infos, required_edges
            )?;
            if let Some(labels) = labels_for_edge.get(&edge_idx) {
                for &label in labels {
                    let linfo = label_infos[(label as usize) - 1];
                    if linfo.len == 1 {
                        bytes_depended_on_by_edge.get_mut(&edge_idx).unwrap()
                            .push(linfo.start_pos);
                    } else {
                        queue.push((edge_idx, linfo.start_pos..(linfo.start_pos + linfo.len)));
                    }
                }
            }
        }
    
        println!("bytes depended on by edge: {:?}", 
            bytes_depended_on_by_edge.iter()
            .filter(|(_,x)| x.len() > 0)
            .collect::<HashMap<&usize, &Vec<usize>>>()
        );

        Ok(bytes_depended_on_by_edge)
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
        println!("Performing dataflowstage");

        let full_neighbours_meta = state
            .metadata::<MapNeighboursFeedbackMetadata>()
            .unwrap();
        let covered_blocks = full_neighbours_meta.covered_blocks.clone();

        let idx = state.corpus().current().unwrap();
        let tc = state.corpus().get(idx).unwrap().borrow();

        // Compute the metadata if not present
        if tc.metadata::<TestcaseDataflowMetadata>().is_err() {
            let covered_meta = tc.metadata::<MapIndexesMetadata>().unwrap();
            let covered_indexes = covered_meta.list.clone();
            {
                let mut cov = covered_indexes.iter().copied().collect::<Vec<usize>>();
                cov.sort();
                println!("corpus index {:?} covered: {:?}", idx, cov);
            }
            drop(tc);

            let direct_neighbours_for_edge: HashMap<usize, Vec<usize>> = {
                let cfg_metadata = state.metadata_mut::<ControlFlowGraph>().unwrap();
                cfg_metadata.get_map_from_edges_to_direct_neighbours(&covered_indexes, &covered_blocks)
            };

            let required_edges: Vec<usize> = direct_neighbours_for_edge.keys().copied().collect();
            let bytes_depended_on_by_edge = self.get_bytes_depended_on_by_edges(
                fuzzer, executor, state, manager, &required_edges)?;

            // println!("corpus_idx {:?}; bytes depended on by edge: {:?}, parents_of_direct_n {:?}", idx, bytes_depended_on_by_edge, parents_of_direct_neighbours);
            
            let meta = TestcaseDataflowMetadata { bytes_depended_on_by_edge, direct_neighbours_for_edge };
            let mut tc = state.corpus().get(idx).unwrap().borrow_mut();
            tc.add_metadata(meta);
        } else {
            drop(tc);
        }

        let tc = state.corpus().get(idx).unwrap().borrow();
        let df_meta = tc.metadata::<TestcaseDataflowMetadata>().unwrap();

        // recalc which edges we've found corpus entries for (so we don't waste time mutating bytes we don't need to)
        let required_edges = {
            let mut req = HashSet::new();
            for (parent, neighbours) in &df_meta.direct_neighbours_for_edge {
                for neighbour in neighbours {
                    if !covered_blocks.contains(neighbour) {
                        req.insert(*parent);
                        break;
                    }
                }
            }
            req
        };

        // build a vec of the values of target bytes
        let mut target_byte_pos: Vec<usize> = {
            let mut res = HashSet::new();
            for edge in required_edges {
                if let Some(dependent_bytes) = df_meta.bytes_depended_on_by_edge.get(&edge) {
                    for &byte_pos in dependent_bytes {
                        res.insert(byte_pos);
                    }
                }
            }
            res.into_iter().collect()
        };
        target_byte_pos.sort();

        let original_input = tc.input().as_ref().unwrap().clone();
        let target_bytes = {
            let mut res = vec![];
            for &pos in &target_byte_pos {
                res.push(original_input.bytes()[pos]);
            }
            res
        };
        drop(tc);

        if target_bytes.is_empty() { return Ok(()); }

        println!("corpus_idx: {:?}, mutating the set of target byte pos: {:?}", idx, target_byte_pos);

        let mut mutator = StdScheduledMutator::with_max_stack_pow(havoc_mutations_fixed_length(), 6);

        // mutate these bytes
        for i in 0..128 {

            let mut input = BytesInput::new(target_bytes.clone());

            start_timer!(state);
            let mutated = mutator.mutate(state, &mut input)?;
            mark_feature_time!(state, PerfFeature::Mutate);

            if mutated == MutationResult::Skipped {
                continue;
            }

            let altered_bytes = input.bytes();
            assert!(altered_bytes.len() == target_bytes.len());

            let mut input = original_input.clone();
            let bytes = input.bytes_mut();
            for (arr_idx, dest_pos) in target_byte_pos.iter().enumerate() {
                bytes[*dest_pos] = altered_bytes[arr_idx];
            }
            // println!("Mutated target bytes {:?}, at pos {:?}; end result: {:?}", altered_bytes, target_byte_pos, bytes);

            // Time is measured directly the `evaluate_input` function
            let (untransformed, post) = input.try_transform_into(state)?;
            let (result, corpus_idx) = fuzzer.evaluate_input(state, executor, manager, untransformed)?;
            
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

    fn restart_progress_should_run(&mut self, _: &mut <Self as UsesState>::State) -> Result<bool, libafl::Error> { 
        Ok(true) 
    }

    fn clear_restart_progress(&mut self, _: &mut <Self as UsesState>::State) -> Result<(), libafl::Error> { 
        Ok(()) 
    }

}
