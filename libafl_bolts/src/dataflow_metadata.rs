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

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Metadata indicating the direct neighbours for each edge (for a given testcase)
/// We need this because of indirect function calls not being resolvable otherwise
pub struct TestcaseDirectNeighboursMetadata {
    /// Map from a covered edge to the list of direct uncovered siblings
    pub siblings_for_covered_bb: HashMap<usize, Vec<usize>>,
    /// Map from uncovered bb coverage map index to parent coverage map index
    pub parent_for_uncovered_bb: HashMap<usize, usize>,
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