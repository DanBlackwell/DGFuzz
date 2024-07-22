//! dfsan logic into targets
//! The colorization stage from `colorization()` in afl++
use alloc::vec::Vec;
use core::{fmt::Debug, marker::PhantomData, ops::Range};
use hashbrown::HashMap;
use std::path::PathBuf;
use nix::sys::signal::Signal;


// use crate::libfuzzer_test_one_input;
use libafl_bolts::{
    prelude::{OwnedMutSlice, UnixShMemProvider}, 
    rands::Rand, 
    shmem::{ShMemDescription, ShMemMetadata}, 
    tuples::{tuple_list, tuple_list_type}, 
    AsSliceMut, HasLen
};
use serde::{Deserialize, Serialize};

use libafl::{
    common::HasMetadata, corpus::Corpus, events::{EventFirer, EventRestarter}, executors::{Executor, HasObservers}, feedbacks::{cfg_prescience::ControlFlowGraph, MapIndexesMetadata, MapNeighboursFeedbackMetadata}, inputs::{BytesInput, HasMutatorBytes, HasTargetBytes, UsesInput}, mark_feature_time, mutators::{BitFlipMutator, ByteAddMutator, ByteDecMutator, ByteFlipMutator, ByteIncMutator, ByteInterestingMutator, ByteNegMutator, ByteRandMutator, BytesCopyMutator, BytesRandSetMutator, BytesSetMutator, BytesSwapMutator, DwordAddMutator, DwordInterestingMutator, MutationResult, Mutator, QwordAddMutator, StdScheduledMutator, WordAddMutator, WordInterestingMutator}, prelude::{ForkserverExecutor, HasExecutions, HasSolutions, HitcountsMapObserver, StdMapObserver, TimeObserver }, stages::{mutational::{MutatedTransform, MutatedTransformPost}, Stage}, start_timer, state::{HasCorpus, HasRand, UsesState}, Error, Evaluator, ExecuteInputResult, HasObjective
};

#[derive(Clone,Debug,Serialize,Deserialize)]
struct FuzzerDataflowMetadata {
    /// Number of mutations tested for a given target edge (neighbour)
    pub num_mutations_for_edge: HashMap<usize, usize>,
}

libafl_bolts::impl_serdeany!(FuzzerDataflowMetadata);

#[derive(Clone,Debug,Serialize,Deserialize)]
struct TestcaseDataflowMetadata {
    /// Map from a covered edge to the list of direct neigbours
    pub direct_neighbours_for_edge: HashMap<usize, Vec<usize>>,
    /// Map from edge index to bytes that the conditional afterwards depends on
    pub bytes_depended_on_by_edge: HashMap<usize, Vec<usize>>,
    /// number of mutations applied to edge
    pub mutations_tested_on_edge: HashMap<usize, usize>,
}

libafl_bolts::impl_serdeany!(TestcaseDataflowMetadata);

#[derive(Copy,Clone,Debug)]
struct DFSanLabelInfo {
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
    mutations_per_stage: usize,
    #[allow(clippy::type_complexity)]
    phantom: PhantomData<(E, EM, Z)>,
}

impl<'a, EM, E, Z> DataflowStage<'a, EM, E, Z>
where 
    E: UsesState + UsesInput, 
    E::State: HasRand + HasMetadata,
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
        let edges_observer = HitcountsMapObserver::new(
            StdMapObserver::from_ownedref("edges_map", cov_map_slice)
        );

        // Create an observation channel to keep track of the execution time
        let time_observer = TimeObserver::new("time");
    
        let mut fs_builder = ForkserverExecutor::builder()
            .program(dfsan_binary_path)
            .shmem_provider(shmem_provider, input_shmem_desc)
            .debug_child(true)
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
            phantom: PhantomData 
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
        required_edges: &[usize],
    ) -> Result<HashMap<u8, Vec<usize>>, Error>
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

        self.executor.run_target(fuzzer, state, manager, input)?;

        let mut edges_for_label: HashMap<u8, Vec<usize>> = HashMap::new();
        for &edge_num in required_edges {
            if buf[edge_num] != 0 {
                let the_byte = buf[edge_num];
                for bit in 0..8 {
                    if (the_byte >> bit) & 1 == 1 {
                        let label_num = bit + 1;
                        if let Some(edges) = edges_for_label.get_mut(&label_num) {
                            edges.push(edge_num);
                        } else {
                            edges_for_label.insert(label_num, vec![edge_num]);
                        }
                    }
                }
                buf[edge_num] = 0;
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
            if range.len() > 8 {
                let mut prev_end = 0usize;
                for idx in 1..9 {
                    let end = (idx as f64 / 8f64 * range.len() as f64).floor() as usize;
                    let len = end - prev_end;
                    labels.push(DFSanLabelInfo { start_pos: range.start + prev_end, len });
                    prev_end = end;
                }
            } else {
                for idx in 0..range.len() {
                    labels.push(DFSanLabelInfo { start_pos: range.start + idx, len: 1 });
                }
            }
            labels
        }
    
        let mut bytes_depended_on_by_edge = {
            let mut tmp = HashMap::new();
            for e in required_edges { tmp.insert(*e, vec![]); }
            tmp
        };
    
        let mut queue = vec![(required_edges.to_vec(), 0..input.bytes().len())];
    
        // Collect up a list of bytes that each edge depends on; these may be disjoint 
        // e.g. if (data[0] + data[3] - data[5] == 0)
        while let Some((required_edges, byte_range)) = queue.pop() {
            let label_infos = get_labels_for_range(byte_range);
            let edges_for_label = self.run_and_collect_labels(
                fuzzer, executor, state, manager, &input, &label_infos, &required_edges
            )?;

            for (label, edges) in edges_for_label {
                let linfo = label_infos[(label as usize) - 1];
                if linfo.len == 1 {
                    for edge_idx in edges {
                        bytes_depended_on_by_edge
                            .get_mut(&edge_idx).unwrap()
                            .push(linfo.start_pos);
                    }
                } else {
                    queue.push((edges, linfo.start_pos..(linfo.start_pos + linfo.len)));
                }
            }
        }

        for (_edge_idx, bytes) in bytes_depended_on_by_edge.iter_mut() {
            bytes.sort();
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

        if state.metadata::<FuzzerDataflowMetadata>().is_err() {
            state.add_metadata(
                FuzzerDataflowMetadata { num_mutations_for_edge: HashMap::new() }
            );
        }

        let num_mutations = 1 + state.rand_mut().below(self.mutations_per_stage);

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
            let bytes_depended_on_by_edge = self.get_bytes_depended_on_by_edges(
                fuzzer, executor, state, manager, &required_edges)?;

            // println!("corpus_idx {:?}; bytes depended on by edge: {:?}, parents_of_direct_n {:?}", idx, bytes_depended_on_by_edge, parents_of_direct_neighbours);
            let mutations_tested_on_edge: HashMap<usize, usize> = required_edges
                .iter()
                .map(|&e| (e, 0))
                .collect();
            
            let meta = TestcaseDataflowMetadata { 
                bytes_depended_on_by_edge, 
                direct_neighbours_for_edge: direct_neighbours_for_edge.clone(),
                mutations_tested_on_edge,
            };
            let mut tc = state.corpus().get(idx).unwrap().borrow_mut();
            tc.add_metadata(meta);
            drop(tc);

            // Add any new neighbours to the effort tracker
            let global_meta = state.metadata_mut::<FuzzerDataflowMetadata>().unwrap();
            for neighbours in direct_neighbours_for_edge.values() {
                for neighbour in neighbours {
                    if global_meta.num_mutations_for_edge.get(neighbour).is_none() {
                        global_meta.num_mutations_for_edge.insert(*neighbour, 0);
                    }
                }
            }
        } else {
            drop(tc);
        }

        let tc_meta_copy = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            let tc_meta = tc.metadata::<TestcaseDataflowMetadata>().unwrap();
            tc_meta.clone()
        };
        let df_meta = state.metadata::<FuzzerDataflowMetadata>().unwrap();

        let mut power_for_mutation_target = HashMap::new();
        let mut total_muts = 0usize;
        let mut max_power = 0usize;

        // recalc which edges we've found corpus entries for (so we don't waste time mutating bytes we don't need to)
        for (parent, neighbours) in &tc_meta_copy.direct_neighbours_for_edge {
            // if we've already tested every possible value for this edge...
            let dependent_bytes = tc_meta_copy.bytes_depended_on_by_edge[parent].len();
            if dependent_bytes < 3 && 
                tc_meta_copy.mutations_tested_on_edge[parent] >= 256usize.pow(dependent_bytes as u32) {
                continue;
            }

            let mut power = 0;
            for neighbour in neighbours {
                if !covered_blocks.contains(neighbour) {
                    let muts = df_meta.num_mutations_for_edge.get(neighbour).unwrap();
                    power += muts;
                }
            }
            if power > max_power { max_power = power; }
            total_muts += power;
            // println!("adding {power} muts for parent {parent}, total muts now {total_muts}");
            power_for_mutation_target.insert(*parent, power);
        }


        // Calculate how much to mutate the bytes for each target edge
        let mutations_for_parent = {
            let mut res = HashMap::new();
            // we haven't fuzzed any of these yet! Fuzz them all the same amount
            if total_muts == 0 {
                let muts = f64::ceil(
                    num_mutations as f64 / power_for_mutation_target.len() as f64
                ) as usize;

                for (edge, _) in power_for_mutation_target {
                    res.insert(edge, muts);
                }
            // Assign more mutations to underserviced edges
            } else {
                let required_muts = power_for_mutation_target.len() * max_power - total_muts;
                // we can catch all up to the same number of mutations
                if required_muts < num_mutations {
                    let mut available_muts = num_mutations;
                    // make sure that all edges catch up to the same value
                    for (edge, muts) in &power_for_mutation_target {
                        available_muts -= max_power - *muts;
                        res.insert(*edge, max_power - *muts);
                    }
                    
                    // distribute the remaining mutations fairly
                    let power = f64::ceil(
                        available_muts as f64 / power_for_mutation_target.len() as f64
                    ) as usize;

                    for (_edge, muts) in res.iter_mut() {
                        *muts += power;
                    }
                } else {
                    // best effort to even out mutations
                    for (edge, muts) in power_for_mutation_target {
                        // figure out how far this edge is behind proportionally
                        let to_perform = f64::ceil(
                            ((max_power - muts) as f64 / required_muts as f64)
                            * num_mutations as f64
                        ) as usize;

                        if to_perform > 0 {
                            res.insert(edge, to_perform);
                        }
                    }
                }
            }
            res
        };

        let mut mutator = StdScheduledMutator::with_max_stack_pow(
            havoc_mutations_fixed_length(), 6
        );

        let (original_input, bytes_depended_on_by_edge) = {
            let tc = state.corpus().get(idx).unwrap().borrow();
            let tc_meta = tc.metadata::<TestcaseDataflowMetadata>().unwrap();
            (
                tc.input().as_ref().unwrap().clone(),
                tc_meta.bytes_depended_on_by_edge.clone(),
            )
        };

        // iterate through all of the edges with uncovered neighbours and test out
        // num_mutations different mutants
        for (parent, num_mutations) in &mutations_for_parent {
            let target_byte_pos = bytes_depended_on_by_edge.get(parent).unwrap().clone();

            if target_byte_pos.is_empty() { continue; }

            // build a vec of the values of target bytes
            let target_bytes = {
                let mut res = Vec::with_capacity(target_byte_pos.len());
                for &pos in &target_byte_pos {
                    res.push(original_input.bytes()[pos]);
                }
                res
            };

            // println!("For parent {parent} running {num_mutations} mutations on bytes {:?}", target_byte_pos);
            let target_bytes_input = BytesInput::new(target_bytes.clone());

            // test out num_mutations different mutants
            for _ in 0..*num_mutations {
                let mut input = target_bytes_input.clone();

                let altered_bytes = if input.bytes().len() >= 3 {
                    // There are a few bytes to mutate here, use the mutator
                    start_timer!(state);
                    let mutated = mutator.mutate(state, &mut input)?;
                    mark_feature_time!(state, PerfFeature::Mutate);

                    if mutated == MutationResult::Skipped {
                        continue;
                    }

                    input.bytes()
                } else {
                    // There are 1 or 2 bytes here - we can do an exhaustive search
                    let bytes = input.bytes_mut();

                    let mut tc = state.corpus_mut().get(idx).unwrap().borrow_mut();
                    let tc_meta = tc.metadata_mut::<TestcaseDataflowMetadata>().unwrap();
                    let tested_vals = tc_meta.mutations_tested_on_edge.get_mut(parent).unwrap();
                    if *tested_vals >= 256usize.pow(bytes.len() as u32) {
                        println!("Dataflow Finished all possible combos for {parent} ({tested_vals})");
                        // We've tested all combinations - bail
                        break;
                    }


                    for idx in 0..bytes.len() {
                        bytes[idx] = ((*tested_vals & 0xFF) >> (8 * idx)) as u8;
                    }
                    *tested_vals += 1;

                    input.bytes()
                };

                let mut input = original_input.clone();
                let bytes = input.bytes_mut();
                // replace the target bytes with the mutated byte values
                for (arr_idx, dest_pos) in target_byte_pos.iter().enumerate() {
                    bytes[*dest_pos] = altered_bytes[arr_idx];
                }

                // Time is measured directly the `evaluate_input` function
                let (untransformed, post) = input.try_transform_into(state)?;
                let (result, corpus_idx) = fuzzer.evaluate_input(state, executor, manager, untransformed)?;
            
                if result == ExecuteInputResult::Corpus {
                    println!("Dataflow stage found a new corpus entry! (through exhaustive testing: {})",
                        target_bytes_input.len() < 3);
                }

                start_timer!(state);
                mutator.post_exec(state, corpus_idx)?;
                post.post_exec(state, corpus_idx)?;
                mark_feature_time!(state, PerfFeature::MutatePostExec);
            }
        }

        {
            // update the mutation counts for all the targets
            let df_meta = state.metadata_mut::<FuzzerDataflowMetadata>().unwrap();
            for (parent, neighbours) in tc_meta_copy.direct_neighbours_for_edge {
                if let Some(muts) = mutations_for_parent.get(&parent) {
                    for neighbour in &neighbours {
                        let count = df_meta.num_mutations_for_edge.get_mut(neighbour).unwrap();
                        *count += *muts;
                    }
                }
            }
        }

        Ok(())
    }

    fn restart_progress_should_run(&mut self, _: &mut <Self as UsesState>::State) -> Result<bool, Error> { 
        Ok(true) 
    }

    fn clear_restart_progress(&mut self, _: &mut <Self as UsesState>::State) -> Result<(), Error> { 
        Ok(()) 
    }

}
