use serde::{Serialize, Deserialize};
use hashbrown::{HashMap, HashSet};
use crate::Vec;

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Fuzzer (global) level metadata for DFSan stage
pub struct FuzzerDataflowMetadata {
    /// Number of mutations tested for a given target edge (neighbour)
    pub num_mutations_for_edge: HashMap<usize, usize>,
}

crate::impl_serdeany!(FuzzerDataflowMetadata);

#[no_mangle]
/// array of edge indexes covered by the current input
pub static mut libafl_path_edge_idxs: [u32; 64 * 1024 * 1024] = [0; 64 * 1024 * 1024];
#[no_mangle]
/// current position in `libafl_path_edge_idxs`
pub static mut libafl_path_filled: u32 = 0;

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Metadata indicating the direct neighbours for each edge (for a given testcase)
/// We need this because of indirect function calls not being resolvable otherwise
pub struct TestcaseDirectNeighboursMetadata {
    /// Map from an uncovered bb coverage map index to its sancov predecessor
    pub sancov_predecessor_for_edge: HashMap<usize, usize>,
    /// Map from a covered edge to the list of direct uncovered siblings
    pub siblings_for_edge: HashMap<usize, Vec<usize>>,
}

crate::impl_serdeany!(TestcaseDirectNeighboursMetadata);

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Testcase level metadata for DFSan stage
pub struct TestcaseDataflowMetadata {
    /// Map from bb coverage map index to bytes that the conditional afterwards depends on
    pub bytes_depended_on_by_uncovered_bb: HashMap<usize, Vec<usize>>,
    /// number of mutations applied to target bytes
    pub mutations_tested_on_target_bytes: HashMap<Vec<usize>, usize>,
    /// set of bb coverage map indexes that depend on a certain set of bytes
    pub uncovered_bbs_depending_on_bytes: HashMap<Vec<usize>, HashSet<usize>>,
}

crate::impl_serdeany!(TestcaseDataflowMetadata);