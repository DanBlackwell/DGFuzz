use serde::{Serialize, Deserialize};
use hashbrown::{HashMap, HashSet};
use crate::Vec;
use alloc::rc::Rc;
use core::{borrow::Borrow, ops::Range};

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
    /// Map from a covered edge to the list of all siblings not covered by with input
    pub locally_uncovered_siblings_for_covered_bb: HashMap<usize, Vec<usize>>,
    /// Map from a covered edge to the list of all siblings not covered by any corpus entry
    pub globally_uncovered_siblings_for_covered_bb: HashMap<usize, Vec<usize>>,
    /// Map from uncovered bb coverage map index to parent coverage map index
    pub parent_for_uncovered_bb: HashMap<usize, usize>,
}

crate::impl_serdeany!(TestcaseDirectNeighboursMetadata);

#[derive(Clone,Debug,Eq,Hash,PartialEq,Serialize,Deserialize)]
pub struct DependentBytes { list: Vec<Range<usize>> }

impl DependentBytes {
    pub fn from_list(list: &[usize]) -> Self {
        let mut sorted = list.to_vec();
        sorted.sort();
        Self::from_sorted_vec(&sorted)
    }

    pub fn from_sorted_vec(sorted_vec: &Vec<usize>) -> Self {
        let mut deps = vec![];
        let mut start_idx = None;
        let mut prev_idx = None;
        for &idx in sorted_vec {
            if start_idx.is_none() { 
                start_idx = Some(idx); 
                prev_idx = Some(idx);
            } else {
                if idx != prev_idx.unwrap() + 1 {
                    deps.push(start_idx.unwrap()..(prev_idx.unwrap() + 1));
                    start_idx = Some(idx);
                }
                prev_idx = Some(idx);
            }
        }
        if let Some(start_idx) = start_idx {
            deps.push(start_idx..(prev_idx.unwrap() + 1));
        }

        Self { list: deps }
    }

    pub fn to_list(&self) -> Vec<usize> {
        let mut res = vec![];
        for range in &self.list {
            for idx in range.clone() {
                res.push(idx);
            }
        }
        res
    }

    pub fn raw_ranges(&self) -> &Vec<Range<usize>> {
        &self.list
    }
}

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Testcase level metadata for DFSan stage
pub struct TestcaseDataflowMetadata {
    /// Map from bb coverage map index to bytes that the conditional afterwards depends on
    pub bytes_depended_on_by_uncovered_bb: HashMap<usize, DependentBytes>,
    /// number of mutations applied to target bytes
    pub mutations_tested_on_target_bytes: HashMap<DependentBytes, usize>,
    /// set of bb coverage map indexes that depend on a certain set of bytes
    pub uncovered_bbs_depending_on_bytes: HashMap<DependentBytes, HashSet<usize>>,
}

crate::impl_serdeany!(TestcaseDataflowMetadata);