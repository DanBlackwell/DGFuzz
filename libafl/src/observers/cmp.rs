//! The `CmpObserver` provides access to the logged values of CMP instructions

use alloc::{borrow::Cow, vec::Vec};
use memchr::memmem;
use core::{
    fmt::Debug,
    marker::PhantomData,
};
use std::borrow::ToOwned;

use c2rust_bitfields::BitfieldStruct;
use hashbrown::{HashMap, HashSet};
use libafl_bolts::{dataflow_metadata::{TestcaseDataflowMetadata, TestcaseDirectNeighboursMetadata}, ownedref::OwnedRefMut, serdeany::SerdeAny, Named};
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::{corpus::Corpus, executors::ExitKind, inputs::{HasMutatorBytes, UsesInput}, observers::Observer, state::HasCorpus, Error, HasMetadata};
use crate::prelude::MapNeighboursFeedbackMetadata;

/// Generic metadata trait for use in a `CmpObserver`, which adds comparisons from a `CmpObserver`
/// primarily intended for use with `AFLppCmpValuesMetadata` or `CmpValuesMetadata`
pub trait CmpObserverMetadata<'a, CM, S>: SerdeAny + Debug + Clone
where
    CM: CmpMap + Debug,
{
    /// Extra data used by the metadata when adding information from a `CmpObserver`, for example
    /// the `original` field in `AFLppCmpLogObserver`
    type Data: 'a + Debug + Default + Serialize + DeserializeOwned;

    /// Instantiate a new metadata instance. This is used by `CmpObserver` to create a new
    /// metadata if one is missing and `add_meta` is specified. This will typically juse call
    /// `new()`
    fn new_metadata() -> Self;

    /// Add comparisons to a metadata from a `CmpObserver`. `cmp_map` is mutable in case
    /// it is needed for a custom map, but this is not utilized for `CmpObserver` or
    /// `AFLppCmpLogObserver`.
    fn add_from(&mut self, usable_count: usize, cmp_map: &mut CM, cmp_observer_data: Self::Data, state: &S);
}

/// Compare values collected during a run
#[derive(Eq, PartialEq, Debug, Serialize, Deserialize, Clone)]
pub enum CmpValues {
    /// Two u8 values
    U8((u8, u8)),
    /// Two u16 values
    U16((u16, u16)),
    /// Two u32 values
    U32((u32, u32)),
    /// Two u64 values
    U64((u64, u64)),
    /// Two vecs of u8 values/byte
    Bytes((Vec<u8>, Vec<u8>)),
}

impl CmpValues {
    /// Returns if the values are numericals
    #[must_use]
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            CmpValues::U8(_) | CmpValues::U16(_) | CmpValues::U32(_) | CmpValues::U64(_)
        )
    }

    /// Converts the value to a u64 tuple
    #[must_use]
    pub fn to_u64_tuple(&self) -> Option<(u64, u64)> {
        match self {
            CmpValues::U8(t) => Some((u64::from(t.0), u64::from(t.1))),
            CmpValues::U16(t) => Some((u64::from(t.0), u64::from(t.1))),
            CmpValues::U32(t) => Some((u64::from(t.0), u64::from(t.1))),
            CmpValues::U64(t) => Some(*t),
            CmpValues::Bytes(_) => None,
        }
    }
}


/// A state metadata holding a list of values logged from comparisons
#[derive(Clone, Debug, Default, Serialize, Deserialize, Hash, Eq, PartialEq)]
#[cfg_attr(
    any(not(feature = "serdeany_autoreg"), miri),
    allow(clippy::unsafe_derive_deserialize)
)] // for SerdeAny
pub struct TargetedCmpValReplace {
    /// A `list` of indexes to be replaced.
    #[serde(skip)]
    pub input_byte_indexes: Vec<usize>,
    /// A `list` of the current values (to be replaced)
    #[serde(skip)]
    pub input_byte_values: Vec<u8>,
    /// A `list` of the replacement values
    #[serde(skip)]
    pub replacement_byte_values: Vec<u8>,
    /// Did we have to reverse this?
    #[serde(skip)]
    pub is_little_endian: bool,
}

/// A state metadata holding a list of values logged from comparisons
#[derive(Debug, Default, Serialize, Deserialize, Clone)]
#[cfg_attr(
    any(not(feature = "serdeany_autoreg"), miri),
    allow(clippy::unsafe_derive_deserialize)
)] // for SerdeAny
pub struct CmpValuesMetadata {
    /// A `list` of values.
    #[serde(skip)]
    pub list: Vec<CmpValues>,
    /// A `HashMap` from prev_edge_idx to list of `CmpValues`
    #[serde(skip)]
    pub map: HashMap<usize, Vec<CmpValues>>,
    /// A `list` of possible DFSan targeted replacements
    #[serde(skip)]
    pub targeted_replacements: Vec<TargetedCmpValReplace>,
}

libafl_bolts::impl_serdeany!(CmpValuesMetadata);

// impl Deref for CmpValuesMetadata {
//     type Target = [CmpValues];
//     fn deref(&self) -> &[CmpValues] {
//         &self.list
//     }
// }

// impl DerefMut for CmpValuesMetadata {
//     fn deref_mut(&mut self) -> &mut [CmpValues] {
//         &mut self.list
//     }
// }

impl CmpValuesMetadata {
    /// Creates a new [`struct@CmpValuesMetadata`]
    #[must_use]
    pub fn new() -> Self {
        Self { list: vec![], map: HashMap::new(), targeted_replacements: vec![] }
    }

    fn populate_targeted_replacements<S>(&mut self, state: &S)
    where
        S: HasMetadata + HasCorpus,
        S::Input: HasMutatorBytes,
    {
        if self.list.is_empty() { return; }

        let curr_idx = state.corpus().current().unwrap();
        let tc = state.corpus().get(curr_idx).unwrap().borrow();
        let Some(df_meta) = tc.metadata_map().get::<TestcaseDataflowMetadata>() else {
            return;
        };
        let dn_meta: &TestcaseDirectNeighboursMetadata = tc.metadata_map().get().unwrap();
        let input = tc.input().as_ref().unwrap();

        let full_neighbours_meta = state
            .metadata::<MapNeighboursFeedbackMetadata>()
            .unwrap();
        let covered_blocks = full_neighbours_meta.covered_blocks.clone();

        let mut all_replacements: HashSet<TargetedCmpValReplace> = HashSet::new();

        for (bb_cov_map_idx, byte_indexes) in &df_meta.bytes_depended_on_by_uncovered_bb {
            if byte_indexes.raw_ranges().is_empty() { continue; }
            // filter out any globally covered edges
            if covered_blocks.contains(bb_cov_map_idx) { continue; }
            let Some(parent) = dn_meta.parent_for_uncovered_bb.get(bb_cov_map_idx) else { continue; };
            let Some(cmpvals) = self.map.get(parent) else { continue; };
            if cmpvals.is_empty() { continue; }

            let trimmed_cmps = cmpvals.into_iter()
                .map(|c| {
                    // convert to vecs
                    let (buf1, buf2) = match c {
                        // makes no sense to strip u8 or u16s
                        CmpValues::U8(v) => return (vec![v.0], vec![v.1]),
                        CmpValues::U16(v) => return (v.0.to_be_bytes().to_vec(), v.1.to_be_bytes().to_vec()),
                        CmpValues::U32(v) => (v.0.to_be_bytes().to_vec(), v.1.to_be_bytes().to_vec()),
                        CmpValues::U64(v) => (v.0.to_be_bytes().to_vec(), v.1.to_be_bytes().to_vec()),
                        CmpValues::Bytes(v) => (v.0.to_owned(), v.1.to_owned())
                    };

                    // strip leading and trailing zeroes
                    let mut start = 0;
                    for idx in 0..buf1.len() {
                        start = idx;
                        if buf1[idx] != 0 || buf1[idx] != buf2[idx] {
                            break;
                        }
                    }
                    let mut end = buf1.len();
                    loop {
                        if buf1[end - 1] != 0 || buf1[end - 1] != buf2[end - 1] {
                            break;
                        }
                        if end == 1 { break; } else { end -= 1; }
                    }

                    // println!("stripping {:?} to range {start}..{end}", c);
                    if start < end {
                        (buf1[start..end].to_vec(), buf2[start..end].to_vec())
                    } else {
                        (vec![], vec![])
                    }
                });

            for range in byte_indexes.raw_ranges() {
                let byte_vals: Vec<u8> = {
                    let buf = input.bytes();
                    range.clone().map(|pos| buf[pos]).collect()
                };

                let expanded_range: Vec<usize> = range.clone().collect();

                // populate a complete list of matches for this cmpval in this edges dependent bytes
                for (cmp1, cmp2) in trimmed_cmps.clone() {
                    // skip boring replacements
                    if cmp1.len() < 1 || byte_vals.len() < cmp1.len() { continue; }

                    // collect up matches for cmpval side 1
                    memmem::find_iter(&byte_vals, &cmp1)
                        .map(|idx| TargetedCmpValReplace {
                            input_byte_indexes: expanded_range[idx..(idx + cmp1.len())].to_vec(),
                            input_byte_values: byte_vals[idx..(idx + cmp1.len())].to_vec(),
                            replacement_byte_values: cmp2.clone(),
                            is_little_endian: false
                        })
                        .for_each(|v| { all_replacements.insert(v); });
                    // if it's a palindrome we'll match it either direction
                    let rev: Vec<u8> = cmp1.clone().into_iter().rev().collect();
                    if cmp1 != rev {
                        memmem::find_iter(&byte_vals, &rev)
                            .map(|idx| TargetedCmpValReplace {
                                input_byte_indexes: expanded_range[idx..(idx + cmp1.len())].to_vec(),
                                input_byte_values: byte_vals[idx..(idx + cmp1.len())].to_vec(),
                                replacement_byte_values: rev.clone(),
                                is_little_endian: true
                            })
                            .for_each(|v| { all_replacements.insert(v); });
                    }

                    // collect up matches for cmpval side 2
                    memmem::find_iter(&byte_vals, &cmp2)
                        .map(|idx| TargetedCmpValReplace {
                            input_byte_indexes: expanded_range[idx..(idx + cmp1.len())].to_vec(),
                            input_byte_values: byte_vals[idx..(idx + cmp1.len())].to_vec(),
                            replacement_byte_values: cmp1.clone(),
                            is_little_endian: false
                        })
                        .for_each(|v| { all_replacements.insert(v); });
                    // if it's a palindrome we'll match it either direction
                    let rev: Vec<u8> = cmp2.clone().into_iter().rev().collect();
                    if cmp2 != rev {
                        memmem::find_iter(&byte_vals, &rev)
                            .map(|idx| TargetedCmpValReplace {
                                input_byte_indexes: expanded_range[idx..(idx + cmp1.len())].to_vec(),
                                input_byte_values: byte_vals[idx..(idx + cmp1.len())].to_vec(),
                                replacement_byte_values: rev.clone(),
                                is_little_endian: true
                            })
                            .for_each(|v| { all_replacements.insert(v); });
                    }
                }
            }
        }

        self.targeted_replacements = all_replacements.into_iter().collect();
    }
}

impl<'a, CM, S> CmpObserverMetadata<'a, CM, S> for CmpValuesMetadata
where
    CM: CmpMap,
        S: HasMetadata + HasCorpus,
        S::Input: HasMutatorBytes,
{
    type Data = bool;

    #[must_use]
    fn new_metadata() -> Self {
        Self::new()
    }

    fn add_from(&mut self, usable_count: usize, cmp_map: &mut CM, _: Self::Data, state: &S) 
    {
        self.list.clear();
        self.map.clear();
        self.targeted_replacements.clear();
        let count = usable_count;
        for i in 0..count {
            let execs = cmp_map.usable_executions_for(i);
            if execs > 0 {
                // Recongize loops and discard if needed
                if execs > 4 {
                    let mut increasing_v0 = 0;
                    let mut increasing_v1 = 0;
                    let mut decreasing_v0 = 0;
                    let mut decreasing_v1 = 0;

                    let mut last: Option<CmpValues> = None;
                    for j in 0..execs {
                        if let Some(val) = cmp_map.values_of(i, j) {
                            if let Some(l) = last.and_then(|x| x.to_u64_tuple()) {
                                if let Some(v) = val.to_u64_tuple() {
                                    if l.0.wrapping_add(1) == v.0 {
                                        increasing_v0 += 1;
                                    }
                                    if l.1.wrapping_add(1) == v.1 {
                                        increasing_v1 += 1;
                                    }
                                    if l.0.wrapping_sub(1) == v.0 {
                                        decreasing_v0 += 1;
                                    }
                                    if l.1.wrapping_sub(1) == v.1 {
                                        decreasing_v1 += 1;
                                    }
                                }
                            }
                            last = Some(val);
                        }
                    }
                    // We check for execs-2 because the logged execs may wrap and have something like
                    // 8 9 10 3 4 5 6 7
                    if increasing_v0 >= execs - 2
                        || increasing_v1 >= execs - 2
                        || decreasing_v0 >= execs - 2
                        || decreasing_v1 >= execs - 2
                    {
                        continue;
                    }
                }

                let cov_map_idx = cmp_map.cov_map_idx_for(i);
                if !self.map.contains_key(&cov_map_idx) {
                    self.map.insert(cov_map_idx, vec![]);
                }
                let vals = self.map
                    .get_mut(&cov_map_idx)
                    .unwrap();

                for j in 0..execs {
                    if let Some(val) = cmp_map.values_of(i, j) {
                        self.list.push(val.clone());
                        vals.push(val);
                    }
                }
            }
        }

        self.populate_targeted_replacements(state);
    }
}

/// A [`CmpMap`] traces comparisons during the current execution
pub trait CmpMap: Debug {
    /// Get the number of cmps
    fn len(&self) -> usize;

    /// Get if it is empty
    #[must_use]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the coverage map index for the cmp at `idx`
    fn cov_map_idx_for(&self, idx: usize) -> usize;

    /// Get the number of executions for a cmp
    fn executions_for(&self, idx: usize) -> usize;

    /// Get the number of logged executions for a cmp
    fn usable_executions_for(&self, idx: usize) -> usize;

    /// Get the logged values for a cmp
    fn values_of(&self, idx: usize, execution: usize) -> Option<CmpValues>;

    /// Reset the state
    fn reset(&mut self) -> Result<(), Error>;
}

/// A [`CmpObserver`] observes the traced comparisons during the current execution using a [`CmpMap`]
pub trait CmpObserver<'a, CM, S, M>: Observer<S>
where
    CM: CmpMap,
    S: UsesInput,
    M: CmpObserverMetadata<'a, CM, S>,
{
    /// Get the number of usable cmps (all by default)
    fn usable_count(&self) -> usize;

    /// Get the `CmpMap`
    fn cmp_map(&self) -> &CM;

    /// Get the `CmpMap` (mutable)
    fn cmp_map_mut(&mut self) -> &mut CM;

    /// Get the observer data. By default, this is the default metadata aux data, which is `()`.
    fn cmp_observer_data(&self) -> M::Data {
        M::Data::default()
    }

    /// Add [`struct@CmpValuesMetadata`] to the State including the logged values.
    /// This routine does a basic loop filtering because loop index cmps are not interesting.
    fn add_cmpvalues_meta(&mut self, state: &mut S)
    where
        S: HasMetadata + HasCorpus,
    {
        let mut meta = state.metadata_map_mut().remove::<M>()
            .map_or_else(|| M::new_metadata(), |x| *x);
        // let mut meta = M::new_metadata();

        let usable_count = self.usable_count();
        let cmp_observer_data = self.cmp_observer_data();

        meta.add_from(usable_count, self.cmp_map_mut(), cmp_observer_data, state);

        state.add_metadata(meta);
    }
}

/// A standard [`CmpObserver`] observer
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound = "CM: serde::de::DeserializeOwned")]
pub struct StdCmpObserver<'a, CM, S, M>
where
    CM: CmpMap + Serialize,
    S: UsesInput + HasMetadata + HasCorpus,
    M: CmpObserverMetadata<'a, CM, S>,
{
    cmp_map: OwnedRefMut<'a, CM>,
    size: Option<OwnedRefMut<'a, usize>>,
    name: Cow<'static, str>,
    add_meta: bool,
    data: M::Data,
    phantom: PhantomData<S>,
}

impl<'a, CM, S, M> CmpObserver<'a, CM, S, M> for StdCmpObserver<'a, CM, S, M>
where
    CM: CmpMap + Serialize + DeserializeOwned,
    S: UsesInput + Debug + HasMetadata + HasCorpus,
    M: CmpObserverMetadata<'a, CM, S>,
{
    /// Get the number of usable cmps (all by default)
    fn usable_count(&self) -> usize {
        match &self.size {
            None => self.cmp_map.as_ref().len(),
            Some(o) => *o.as_ref(),
        }
    }

    fn cmp_map(&self) -> &CM {
        self.cmp_map.as_ref()
    }

    fn cmp_map_mut(&mut self) -> &mut CM {
        self.cmp_map.as_mut()
    }

    fn cmp_observer_data(&self) -> <M as CmpObserverMetadata<'a, CM, S>>::Data {
        <M as CmpObserverMetadata<CM, S>>::Data::default()
    }
}

impl<'a, CM, S, M> Observer<S> for StdCmpObserver<'a, CM, S, M>
where
    CM: CmpMap + Serialize + DeserializeOwned,
    S: UsesInput + Debug + HasMetadata + HasCorpus,
    M: CmpObserverMetadata<'a, CM, S>,
{
    fn pre_exec(&mut self, _state: &mut S, _input: &S::Input) -> Result<(), Error> {
        self.cmp_map.as_mut().reset()?;
        Ok(())
    }

    fn post_exec(
        &mut self,
        state: &mut S,
        _input: &S::Input,
        _exit_kind: &ExitKind,
    ) -> Result<(), Error> {
        if self.add_meta {
            self.add_cmpvalues_meta(state);
        }
        Ok(())
    }
}

impl<'a, CM, S, M> Named for StdCmpObserver<'a, CM, S, M>
where
    CM: CmpMap + Serialize + DeserializeOwned,
    S: UsesInput + HasMetadata + HasCorpus,
    M: CmpObserverMetadata<'a, CM, S>,
{
    fn name(&self) -> &Cow<'static, str> {
        &self.name
    }
}

impl<'a, CM, S, M> StdCmpObserver<'a, CM, S, M>
where
    CM: CmpMap + Serialize + DeserializeOwned,
    S: UsesInput + HasMetadata + HasCorpus,
    M: CmpObserverMetadata<'a, CM, S>,
{
    /// Creates a new [`StdCmpObserver`] with the given name and map.
    #[must_use]
    pub fn new(name: &'static str, map: OwnedRefMut<'a, CM>, add_meta: bool) -> Self {
        Self {
            name: Cow::from(name),
            size: None,
            cmp_map: map,
            add_meta,
            data: M::Data::default(),
            phantom: PhantomData,
        }
    }

    /// Creates a new [`StdCmpObserver`] with the given name, map, and auxiliary data used to
    /// populate metadata
    #[must_use]
    pub fn with_data(
        name: &'static str,
        cmp_map: OwnedRefMut<'a, CM>,
        add_meta: bool,
        data: M::Data,
    ) -> Self {
        Self {
            name: Cow::from(name),
            size: None,
            cmp_map,
            add_meta,
            data,
            phantom: PhantomData,
        }
    }

    /// Creates a new [`StdCmpObserver`] with the given name, map and reference to variable size.
    #[must_use]
    pub fn with_size(
        name: &'static str,
        cmp_map: OwnedRefMut<'a, CM>,
        add_meta: bool,
        size: OwnedRefMut<'a, usize>,
    ) -> Self {
        Self {
            name: Cow::from(name),
            size: Some(size),
            cmp_map,
            add_meta,
            data: M::Data::default(),
            phantom: PhantomData,
        }
    }

    /// Creates a new [`StdCmpObserver`] with the given name, map, auxiliary data, and
    /// reference to variable size.
    #[must_use]
    pub fn with_size_data(
        name: &'static str,
        cmp_map: OwnedRefMut<'a, CM>,
        add_meta: bool,
        data: M::Data,
        size: OwnedRefMut<'a, usize>,
    ) -> Self {
        Self {
            name: Cow::from(name),
            size: Some(size),
            cmp_map,
            add_meta,
            data,
            phantom: PhantomData,
        }
    }

    /// Handle the stored auxiliary data associated with the [`CmpObserverMetadata`]
    pub fn data(&self) -> &M::Data {
        &self.data
    }

    /// Mutably reference the stored auxiliary data associated with the [`CmpObserverMetadata`]
    pub fn data_mut(&mut self) -> &mut M::Data {
        &mut self.data
    }
}

/// A [`StdCmpObserver`] that optionally adds comparisons into a [`CmpValuesMetadata`]
pub type StdCmpValuesObserver<'a, CM, S> = StdCmpObserver<'a, CM, S, CmpValuesMetadata>;

/* From AFL++ cmplog.h

#define CMP_MAP_W 65536
#define CMP_MAP_H 32
#define CMP_MAP_RTN_H (CMP_MAP_H / 4)

struct cmp_header {

  unsigned hits : 24;
  unsigned id : 24;
  unsigned shape : 5;
  unsigned type : 2;
  unsigned attribute : 4;
  unsigned overflow : 1;
  unsigned reserved : 4;

} __attribute__((packed));

struct cmp_operands {

  u64 v0;
  u64 v1;
  u64 v0_128;
  u64 v1_128;

} __attribute__((packed));

struct cmpfn_operands {

  u8 v0[31];
  u8 v0_len;
  u8 v1[31];
  u8 v1_len;

} __attribute__((packed));

typedef struct cmp_operands cmp_map_list[CMP_MAP_H];

struct cmp_map {

  struct cmp_header   headers[CMP_MAP_W];
  struct cmp_operands log[CMP_MAP_W][CMP_MAP_H];

};
*/

/// A state metadata holding a list of values logged from comparisons. AFL++ RQ version.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[cfg_attr(
    any(not(feature = "serdeany_autoreg"), miri),
    allow(clippy::unsafe_derive_deserialize)
)] // for SerdeAny
pub struct AFLppCmpValuesMetadata {
    /// The first map of `AFLppCmpLogVals` retrieved by running the un-mutated input
    #[serde(skip)]
    pub orig_cmpvals: HashMap<usize, Vec<CmpValues>>,
    /// The second map of `AFLppCmpLogVals` retrieved by runnning the mutated input
    #[serde(skip)]
    pub new_cmpvals: HashMap<usize, Vec<CmpValues>>,
    /// The list of logged idx and headers retrieved by runnning the mutated input
    #[serde(skip)]
    pub headers: Vec<(usize, AFLppCmpLogHeader)>,
}

libafl_bolts::impl_serdeany!(AFLppCmpValuesMetadata);

impl AFLppCmpValuesMetadata {
    /// Constructor for `AFLppCmpValuesMetadata`
    #[must_use]
    pub fn new() -> Self {
        Self {
            orig_cmpvals: HashMap::new(),
            new_cmpvals: HashMap::new(),
            headers: Vec::new(),
        }
    }

    /// Getter for `orig_cmpvals`
    #[must_use]
    pub fn orig_cmpvals(&self) -> &HashMap<usize, Vec<CmpValues>> {
        &self.orig_cmpvals
    }

    /// Getter for `new_cmpvals`
    #[must_use]
    pub fn new_cmpvals(&self) -> &HashMap<usize, Vec<CmpValues>> {
        &self.new_cmpvals
    }

    /// Getter for `headers`
    #[must_use]
    pub fn headers(&self) -> &Vec<(usize, AFLppCmpLogHeader)> {
        &self.headers
    }
}

#[derive(Debug, Copy, Clone, BitfieldStruct)]
#[repr(C, packed)]
/// Comparison header, used to describe a set of comparison values efficiently.
///
/// # Bitfields
///
/// - hits:      The number of hits of a particular comparison
/// - id:        Unused by ``LibAFL``, a unique ID for a particular comparison
/// - shape:     Whether a comparison is u8/u8, u16/u16, etc.
/// - _type:     Whether the comparison value represents an instruction (like a `cmp`) or function
///              call arguments
/// - attribute: OR-ed bitflags describing whether the comparison is <, >, =, <=, >=, or transform
/// - overflow:  Whether the comparison overflows
/// - reserved:  Reserved for future use
pub struct AFLppCmpLogHeader {
    /// The header values
    #[bitfield(name = "hits", ty = "u32", bits = "0..=5")] // 6 bits up to 63 entries, we have CMP_MAP_H = 32 (so using half of it)
    #[bitfield(name = "shape", ty = "u32", bits = "6..=10")] // 31 + 1 bytes max
    #[bitfield(name = "_type", ty = "u8", bits = "11..=11")] // 2: cmp, rtn
    #[bitfield(name = "attribute", ty = "u32", bits = "12..=15")]
    // 16 types for arithmetic comparison types
    pub data: [u8; 2],
}
