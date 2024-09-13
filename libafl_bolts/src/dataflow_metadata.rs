use serde::{Serialize, Deserialize};
use hashbrown::{HashMap, HashSet};
use crate::Vec;
use core::ops::Range;

/// A wrapper for u32 indicating the Coverage map index for a basic block / instruction
#[derive(Hash,Copy,Clone,Debug,Eq,PartialEq,Serialize,Deserialize)]
pub struct CoverageMapIdx(pub u32);
crate::impl_serdeany!(CoverageMapIdx);

/// A wrapper for u64 indicating the uuid for a basic block
#[derive(Hash,Copy,Clone,Debug,Eq,PartialEq,Serialize,Deserialize)]
pub struct BasicBlockUUID(pub u32);
crate::impl_serdeany!(BasicBlockUUID);

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Fuzzer (global) level metadata for DFSan stage
pub struct FuzzerDataflowMetadata {
    /// Number of mutations tested for a given target edge (neighbour)
    pub num_mutations_for_edge: HashMap<CoverageMapIdx, usize>,
}

crate::impl_serdeany!(FuzzerDataflowMetadata);

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Metadata indicating the direct neighbours for each edge (for a given testcase)
/// We need this because of indirect function calls not being resolvable otherwise
pub struct TestcaseDirectNeighboursMetadata {
    /// Set of `CoverageMapIdx` containing all uncovered bbs (by this input) that have covered siblings
    pub locally_uncovered_bbs_that_have_covered_siblings: HashSet<CoverageMapIdx>,
    /// Set of `CoverageMapIdx` containing all covered bbs that have uncovered siblings (by this input)
    pub covered_bbs_that_have_locally_uncovered_siblings: HashSet<CoverageMapIdx>,
    /// Map from uncovered bb coverage map index to parent coverage map index
    pub parent_for_uncovered_bb: HashMap<CoverageMapIdx, CoverageMapIdx>,
}

crate::impl_serdeany!(TestcaseDirectNeighboursMetadata);

#[derive(Clone,Debug,Eq,Hash,PartialEq,Serialize,Deserialize)]
/// Struct containing a set of bytes depended on by a branch - internally uses a list of Ranges to save mem
pub struct DependentBytes { list: Vec<Range<usize>> }

impl DependentBytes {
    /// Construct a `DependentBytes` struct from an unsorted list of `usize`
    pub fn from_list(list: &[usize]) -> Self {
        let mut sorted = list.to_vec();
        sorted.sort();
        Self::from_sorted_vec(&sorted)
    }

    /// Construct a `DependentBytes` struct from a sorted `Vec<usize>`
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

    /// Flatten out the internal ranges into a list of indexes
    pub fn to_list(&self) -> Vec<usize> {
        let mut res = vec![];
        for range in &self.list {
            for idx in range.clone() {
                res.push(idx);
            }
        }
        res
    }

    /// Get a reference to the raw underlying ranges of indexes
    pub fn raw_ranges(&self) -> &Vec<Range<usize>> {
        &self.list
    }
}

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Testcase level metadata for DFSan stage
pub struct TestcaseDataflowMetadata {
    /// number of mutations applied to target bytes
    pub mutations_tested_on_target_bytes: HashMap<DependentBytes, usize>,
    /// set of bb coverage map indexes that depend on a certain set of bytes
    pub uncovered_bbs_depending_on_bytes: HashMap<DependentBytes, HashSet<CoverageMapIdx>>,
}

crate::impl_serdeany!(TestcaseDataflowMetadata);