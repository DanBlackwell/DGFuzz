//! dfsan logic into targets
//! The colorization stage from `colorization()` in afl++
use alloc::{
    borrow::ToOwned, collections::binary_heap::BinaryHeap, string::{String, ToString}, vec::Vec
};
use core::{cmp::Ordering, fmt::Debug, marker::PhantomData, ops::Range};
use hashbrown::{HashMap, HashSet};

use crate::libfuzzer_test_one_input;
use libafl_bolts::{rands::Rand, tuples::{tuple_list, tuple_list_type, MatchName}, AsSlice};
use serde::{Deserialize, Serialize};

use libafl::{
    corpus::{Corpus, HasCurrentCorpusIdx}, events::{EventFirer, EventRestarter}, executors::{Executor, ExitKind, HasObservers, InProcessExecutor}, feedbacks::{cfg_prescience::ControlFlowGraph, MapIndexesMetadata, MapNeighboursFeedbackMetadata}, inputs::{BytesInput, HasBytesVec, HasTargetBytes, UsesInput}, mark_feature_time, mutators::{BitFlipMutator, ByteAddMutator, ByteDecMutator, ByteFlipMutator, ByteIncMutator, ByteInterestingMutator, ByteNegMutator, ByteRandMutator, BytesCopyMutator, BytesRandSetMutator, BytesSetMutator, BytesSwapMutator, DwordAddMutator, DwordInterestingMutator, MutationResult, Mutator, QwordAddMutator, StdScheduledMutator, WordAddMutator, WordInterestingMutator
    }, observers::{MapObserver, ObserversTuple}, prelude::{HasClientPerfMonitor, HasExecutions, HasSolutions}, stages::{mutational::{MutatedTransform, MutatedTransformPost}, Stage}, start_timer, state::{HasCorpus, HasMetadata, HasRand, UsesState}, Error, Evaluator, HasObjective
};

use libc;
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
#[derive(Clone, Debug)]
pub struct DataflowStage<EM, E, Z> 
// where 
//     E: UsesState + UsesInput, 
//     E::State: HasRand, 
//     E::Input: HasBytesVec 
{
    // mutator: StdScheduledMutator<E::Input, HavocMutationsFixedLengthType, E::State>,
    #[allow(clippy::type_complexity)]
    phantom: PhantomData<(E, EM, Z)>,
}

impl<EM, E, Z> DataflowStage<EM, E, Z>
where 
    E: UsesState + UsesInput, 
    E::State: HasRand, 
    E::Input: HasBytesVec 
{
    pub fn new() -> Self {
        dfsan_init();
        // let mut mutator = StdScheduledMutator::with_max_stack_pow(havoc_mutations_fixed_length(), 6);
        // DataflowStage { mutator, phantom: PhantomData }
        DataflowStage { phantom: PhantomData }
    }

    /// return a hashmap giving a Vec of labels for each edge
    fn run_and_collect_labels(
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
        println!("entered run_and_collect_labels");
        let start_offsets = labels.iter().map(|l| l.start_pos).collect::<Vec<usize>>();
        let lens = labels.iter().map(|l| l.len).collect::<Vec<usize>>();
        let mut input_bytes = input.bytes().to_owned();
        println!("calling tag_input_with_labels(len: {} {:?}, {:?}, {:?})", input_bytes.len(), input_bytes, start_offsets, lens);
        tag_input_with_labels(&mut input_bytes, &start_offsets, &lens);

        let mut labels_for_edge = HashMap::new();
        unsafe {
            for i in 0..dfsan_labels_following_edge.len() {
                if dfsan_labels_following_edge[i] != 0 {
                    let the_byte = dfsan_labels_following_edge[i];
                    let mut labels = vec![];
                    for bit in 0..8 {
                        if (the_byte >> bit) & 1 == 1 {
                            labels.push(bit + 1);
                        }
                    }
                    labels_for_edge.insert(i, labels);
                }
            }
        }

        Ok(labels_for_edge)
    }

    fn get_bytes_depended_on_by_edges(
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
        E::Input: HasBytesVec,
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
            let labels_for_edge = Self::run_and_collect_labels(fuzzer, executor, state, manager, &input, &label_infos)?;
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
    
        println!("bytes depended on by edge: {:?}", bytes_depended_on_by_edge);

        Ok(bytes_depended_on_by_edge)
    }
}

impl<EM, E, Z> UsesState for DataflowStage<EM, E, Z>
where
    E: UsesState + UsesInput,
    E::State: HasRand,
    E::Input: HasBytesVec
{
    type State = E::State;
}

impl<E, EM, Z> Stage<E, EM, Z> for DataflowStage<EM, E, Z>
where
    EM: UsesState<State = E::State> + EventFirer + EventRestarter,
    E: HasObservers + Executor<EM, Z>,
    E::State: HasCorpus + HasMetadata + HasRand + HasExecutions + HasSolutions,
    E::Input: HasBytesVec,
    Z: UsesState<State = E::State> + HasObjective + Evaluator<E, EM>,
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
            drop(tc);

            let direct_neighbours_for_edge: HashMap<usize, Vec<usize>> = {
                let cfg_metadata = state.metadata_mut::<ControlFlowGraph>().unwrap();
                cfg_metadata.get_map_from_edges_to_direct_neighbours(&covered_indexes, &covered_blocks)
            };

            let required_edges: Vec<usize> = direct_neighbours_for_edge.keys().copied().collect();
            let bytes_depended_on_by_edge = Self::get_bytes_depended_on_by_edges(
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

        println!("required edges: {:?}", required_edges);

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

        println!("The set of target byte pos: {:?}", target_byte_pos);

        let original_input = tc.input().as_ref().unwrap().clone();
        let target_bytes = {
            let mut res = vec![];
            for &pos in &target_byte_pos {
                res.push(original_input.bytes()[pos]);
            }
            res
        };
        drop(tc);

        let mut mutator = StdScheduledMutator::with_max_stack_pow(havoc_mutations_fixed_length(), 6);

        // mutate these bytes
        for i in 0..128 {
            let mut input = BytesInput::new(target_bytes.clone());
            println!("Original target bytes: {:?}", input.bytes());

            start_timer!(state);
            let mutated = mutator.mutate(state, &mut input, i)?;
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
            println!("Mutated target bytes {:?}, at pos {:?}; end result: {:?}", altered_bytes, target_byte_pos, bytes);

            // Time is measured directly the `evaluate_input` function
            let (untransformed, post) = input.try_transform_into(state)?;
            let (_, corpus_idx) = fuzzer.evaluate_input(state, executor, manager, untransformed)?;

            start_timer!(state);
            mutator.post_exec(state, i as i32, corpus_idx)?;
            post.post_exec(state, i as i32, corpus_idx)?;
            mark_feature_time!(state, PerfFeature::MutatePostExec);
        }

        Ok(())
    }
}
