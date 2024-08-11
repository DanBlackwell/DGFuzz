use serde::{Serialize, Deserialize};
use hashbrown::HashMap;
use crate::Vec;

#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct FuzzerDataflowMetadata {
    /// Number of mutations tested for a given target edge (neighbour)
    pub num_mutations_for_edge: HashMap<usize, usize>,
}

crate::impl_serdeany!(FuzzerDataflowMetadata);

#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct TestcaseDataflowMetadata {
    /// Map from a covered edge to the list of direct neigbours
    pub direct_neighbours_for_edge: HashMap<usize, Vec<usize>>,
    /// Map from edge index to bytes that the conditional afterwards depends on
    pub bytes_depended_on_by_edge: HashMap<usize, Vec<usize>>,
    /// number of mutations applied to target bytes
    pub mutations_tested_on_target_bytes: HashMap<Vec<usize>, usize>,
    /// list of edges that depend on a certain set of bytes
    pub edges_depending_on_bytes: HashMap<Vec<usize>, Vec<usize>>,
}

crate::impl_serdeany!(TestcaseDataflowMetadata);