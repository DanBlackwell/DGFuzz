//! [`LLVM` `PcGuard`](https://clang.llvm.org/docs/SanitizerCoverage.html#tracing-pcs-with-guards) runtime for `LibAFL`.

use alloc::vec::Vec;
use hashbrown::HashMap;

use core::ptr;
#[rustversion::nightly]
#[cfg(feature = "sancov_ngram4")]
use core::simd::num::SimdUint;

#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ctx"))]
use libafl::executors::{hooks::ExecutorHook, HasObservers};

#[cfg(any(
    feature = "pointer_maps",
    feature = "sancov_pcguard_edges",
    feature = "sancov_pcguard_hitcounts",
    feature = "sancov_ctx",
    feature = "sancov_ngram4",
))]
use crate::coverage::EDGES_MAP;
use crate::coverage::MAX_EDGES_FOUND;
#[cfg(feature = "sancov_ngram4")]
use crate::EDGES_MAP_SIZE_IN_USE;
#[cfg(feature = "pointer_maps")]
use crate::{coverage::EDGES_MAP_PTR, EDGES_MAP_SIZE_MAX};

use once_cell::unsync::Lazy;
use std::collections::HashSet;
static mut SEEN_GUARDS: Lazy<HashSet<u32>> = Lazy::new(|| HashSet::new());
static mut UNUSED_GUARD_INDEXES: Lazy<HashSet<u32>> = Lazy::new(|| HashSet::new());

#[no_mangle]
static mut libafl_last_seen_edge_idx: u32 = 0;

#[cfg(all(feature = "sancov_pcguard_edges", feature = "sancov_pcguard_hitcounts"))]
#[cfg(not(any(doc, feature = "clippy")))]
compile_error!(
    "the libafl_targets `sancov_pcguard_edges` and `sancov_pcguard_hitcounts` features are mutually exclusive."
);

#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
use core::ops::ShlAssign;

#[cfg(feature = "sancov_ngram4")]
#[rustversion::nightly]
type Ngram4 = core::simd::u32x4;

#[cfg(feature = "sancov_ngram8")]
#[rustversion::nightly]
type Ngram8 = core::simd::u32x8;

/// The array holding the previous locs. This is required for NGRAM-4 instrumentation
#[cfg(feature = "sancov_ngram4")]
#[rustversion::nightly]
pub static mut PREV_ARRAY_4: Ngram4 = Ngram4::from_array([0, 0, 0, 0]);

/// The array holding the previous locs. This is required for NGRAM-4 instrumentation
#[cfg(feature = "sancov_ngram8")]
#[rustversion::nightly]
pub static mut PREV_ARRAY_8: Ngram8 = Ngram8::from_array([0, 0, 0, 0, 0, 0, 0, 0]);

/// We shift each of the values in ngram4 everytime we see new edges
#[cfg(feature = "sancov_ngram4")]
#[rustversion::nightly]
pub static SHR_4: Ngram4 = Ngram4::from_array([1, 1, 1, 1]);

/// We shift each of the values in ngram8 everytime we see new edges
#[cfg(feature = "sancov_ngram8")]
#[rustversion::nightly]
pub static SHR_8: Ngram8 = Ngram8::from_array([1, 1, 1, 1, 1, 1, 1, 1]);

#[cfg(any(
    feature = "sancov_ngram4",
    feature = "sancov_ngram8",
    feature = "sancov_ctx"
))]
use core::marker::PhantomData;

/// The hook to initialize ngram everytime we run the harness
#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
#[rustversion::nightly]
#[derive(Debug, Clone, Copy)]
pub struct NgramHook<S>
where
    S: libafl::inputs::UsesInput,
{
    phantom: PhantomData<S>,
}

/// The hook to initialize ctx everytime we run the harness
#[cfg(feature = "sancov_ctx")]
#[derive(Debug, Clone, Copy)]
pub struct CtxHook<S> {
    phantom: PhantomData<S>,
}

#[cfg(feature = "sancov_ctx")]
impl<S> CtxHook<S>
where
    S: libafl::inputs::UsesInput,
{
    /// The constructor for this struct
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

#[cfg(feature = "sancov_ctx")]
impl<S> Default for CtxHook<S>
where
    S: libafl::inputs::UsesInput,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
#[rustversion::nightly]
impl<S> ExecutorHook<S> for NgramHook<S>
where
    S: libafl::inputs::UsesInput,
{
    fn init<E: HasObservers>(&mut self, _state: &mut S) {}
    fn pre_exec(&mut self, _state: &mut S, _input: &S::Input) {
        #[cfg(feature = "sancov_ngram4")]
        unsafe {
            PREV_ARRAY_4 = Ngram4::from_array([0, 0, 0, 0]);
        }

        #[cfg(feature = "sancov_ngram8")]
        unsafe {
            PREV_ARRAY_8 = Ngram8::from_array([0, 0, 0, 0, 0, 0, 0, 0]);
        }
    }
    fn post_exec(&mut self, _state: &mut S, _input: &S::Input) {}
}

#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
#[rustversion::nightly]
impl<S> NgramHook<S>
where
    S: libafl::inputs::UsesInput,
{
    /// The constructor for this struct
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
#[rustversion::nightly]
impl<S> Default for NgramHook<S>
where
    S: libafl::inputs::UsesInput,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "sancov_ctx")]
impl<S> ExecutorHook<S> for CtxHook<S>
where
    S: libafl::inputs::UsesInput,
{
    fn init<E: HasObservers>(&mut self, _state: &mut S) {}
    fn pre_exec(&mut self, _state: &mut S, _input: &S::Input) {
        unsafe {
            __afl_prev_ctx = 0;
        }
    }
    fn post_exec(&mut self, _state: &mut S, _input: &S::Input) {}
}

#[rustversion::nightly]
#[allow(unused)]
#[inline]
#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
unsafe fn update_ngram(pos: usize) -> usize {
    let mut reduced = pos;
    #[cfg(feature = "sancov_ngram4")]
    {
        PREV_ARRAY_4 = PREV_ARRAY_4.rotate_elements_right::<1>();
        PREV_ARRAY_4.shl_assign(SHR_4);
        PREV_ARRAY_4.as_mut_array()[0] = pos as u32;
        reduced = PREV_ARRAY_4.reduce_xor() as usize;
    }
    #[cfg(feature = "sancov_ngram8")]
    {
        PREV_ARRAY_8 = PREV_ARRAY_8.rotate_elements_right::<1>();
        PREV_ARRAY_8.shl_assign(SHR_8);
        PREV_ARRAY_8.as_mut_array()[0] = pos as u32;
        reduced = PREV_ARRAY_8.reduce_xor() as usize;
    }
    reduced %= EDGES_MAP_SIZE_IN_USE;
    reduced
}

#[rustversion::not(nightly)]
#[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
unsafe fn update_ngram(pos: usize) -> usize {
    pos
}

extern "C" {
    /// The ctx variable
    pub static mut __afl_prev_ctx: u32;
}

/// HashMap from pc_guard array index, to the actual guard value at that index
static mut PC_GUARD_ARRAY_INDEX_TO_GUARD_VALUE: Option<HashMap<usize, usize>> = None;

/// Callback for sancov `pc_guard` - usually called by `llvm` on each block or edge.
///
/// # Safety
/// Dereferences `guard`, reads the position from there, then dereferences the [`EDGES_MAP`] at that position.
/// Should usually not be called directly.
#[no_mangle]
#[allow(unused_assignments)]
pub unsafe extern "C" fn __sanitizer_cov_trace_pc_guard(guard: *mut u32) {
    libafl_last_seen_edge_idx = *guard;

    #[allow(unused_mut)]
    let mut pos = *guard as usize;

    #[cfg(any(feature = "sancov_ngram4", feature = "sancov_ngram8"))]
    {
        pos = update_ngram(pos);
        // println!("Wrinting to {} {}", pos, EDGES_MAP_SIZE_IN_USE);
    }

    #[cfg(feature = "sancov_ctx")]
    {
        pos ^= __afl_prev_ctx as usize;
        // println!("Wrinting to {} {}", pos, EDGES_MAP_SIZE_IN_USE);
    }

    #[cfg(feature = "pointer_maps")]
    {
        #[cfg(feature = "sancov_pcguard_edges")]
        {
            EDGES_MAP_PTR.add(pos).write(1);
        }
        #[cfg(feature = "sancov_pcguard_hitcounts")]
        {
            let addr = EDGES_MAP_PTR.add(pos);
            let val = addr.read().wrapping_add(1);
            addr.write(val);
        }
    }
    #[cfg(not(feature = "pointer_maps"))]
    {
        #[cfg(feature = "sancov_pcguard_edges")]
        {
            *EDGES_MAP.get_unchecked_mut(pos) = 1;
        }
        #[cfg(feature = "sancov_pcguard_hitcounts")]
        {
            let val = (*EDGES_MAP.get_unchecked(pos)).wrapping_add(1);
            *EDGES_MAP.get_unchecked_mut(pos) = val;
        }
    }
}

/// Initialize the sancov `pc_guard` - usually called by `llvm`.
///
/// # Safety
/// Dereferences at `start` and writes to it.
#[no_mangle]
pub unsafe extern "C" fn __sanitizer_cov_trace_pc_guard_init(mut start: *mut u32, stop: *mut u32) {
    #[cfg(feature = "pointer_maps")]
    if EDGES_MAP_PTR.is_null() {
        EDGES_MAP_PTR = EDGES_MAP.as_mut_ptr();
    }

    if start == stop {
        //|| *start != 0 {
        return;
    }

    unsafe {
        PC_GUARD_ARRAY_INDEX_TO_GUARD_VALUE = Some(HashMap::new());
    }
    let mut seen = vec![];
    let mut set_seen = HashSet::new();
    let mut dupes = vec![];
    let mut index = 0;
    while start < stop {
        unsafe {
            PC_GUARD_ARRAY_INDEX_TO_GUARD_VALUE
                .as_mut()
                .unwrap()
                .insert(index, *start as usize);
        }
        index += 1;
        seen.push(*start);
        SEEN_GUARDS.insert(*start);
        if !set_seen.insert(*start) {
            dupes.push(*start);
        }
        start = start.offset(1);
    }

    let max = seen.iter().fold(0, |max, &x| if x > max { x } else { max });
    MAX_EDGES_FOUND = max as usize + 1;
    for i in 0..=max {
        if !set_seen.contains(&i) {
            UNUSED_GUARD_INDEXES.insert(i);
        }
    }
}

static mut PCS_BEG: *const usize = ptr::null();
static mut PCS_END: *const usize = ptr::null();
/// PC Table as acquired from SanitizerCoverage
pub static mut SANCOV_PC_TABLE: Option<SanCovPcTable> = None;

#[no_mangle]
unsafe extern "C" fn __sanitizer_cov_pcs_init(pcs_beg: *const usize, pcs_end: *const usize) {
    // "The Unsafe Code Guidelines also notably defines that usize and isize are respectively compatible with uintptr_t and intptr_t defined in C."
    assert!(
        pcs_beg == PCS_BEG || PCS_BEG.is_null(),
        "__sanitizer_cov_pcs_init can be called only once."
    );
    assert!(
        pcs_end == PCS_END || PCS_END.is_null(),
        "__sanitizer_cov_pcs_init can be called only once."
    );

    SANCOV_PC_TABLE = Some(SanCovPcTable::new(pcs_beg, pcs_end));
}

/// An entry to the `sanitizer_cov` `pc_table`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcTableEntry {
    addr: usize,
    flags: usize,
    array_index: usize,
}

impl PcTableEntry {
    /// Returns whether the PC corresponds to a function entry point.
    #[must_use]
    pub fn is_function_entry(&self) -> bool {
        self.flags == 0x1
    }

    /// Returns the address associated with this PC.
    #[must_use]
    pub fn addr(&self) -> usize {
        self.addr
    }

    /// Returns the coverage map index associated with this PC.
    #[must_use]
    pub fn cov_map_idx(&self) -> usize {
        unsafe {
            **PC_GUARD_ARRAY_INDEX_TO_GUARD_VALUE
                .as_ref()
                .unwrap()
                .get(&self.array_index)
                .as_ref()
                .unwrap()
        }
    }
}

#[derive(Debug)]
/// Struct containing the information pulled from SanitizerCoverage's PC table
pub struct SanCovPcTable {
    entries_sorted_addr: Vec<PcTableEntry>,
    entry_for_address_cache: HashMap<usize, PcTableEntry>,
}

impl SanCovPcTable {
    pub(crate) unsafe fn new(pcs_beg: *const usize, pcs_end: *const usize) -> Self {
        // SAFETY: Once pcs_beg and pcs_end have been initialized, will not be written to again. So
        // there's no TOCTOU issue.
        assert!(!pcs_beg.is_null() && !pcs_end.is_null());
        let mut cov_sorted = vec![];
        let mut iter = pcs_beg;
        let mut array_index = 0;
        while iter < pcs_end {
            let entry = PcTableEntry {
                addr: *iter,
                flags: *(iter.wrapping_add(1)),
                array_index,
            };
            iter = iter.wrapping_add(2);
            cov_sorted.push(entry);
            array_index += 1;
        }

        let mut addr_sorted: Vec<PcTableEntry> = cov_sorted.clone();
        addr_sorted.sort_by(|a, b| a.addr().partial_cmp(&b.addr()).unwrap());

        Self {
            entries_sorted_addr: addr_sorted,
            entry_for_address_cache: HashMap::new(),
        }
    }

    /// Get the `PcTableEntry` (from SanCov's PC Table) for a given address (probably the return value of a callback)
    pub fn entry_containing_address(&mut self, address: usize) -> Option<PcTableEntry> {
        if let Some(entry) = self.entry_for_address_cache.get(&address) {
            return Some(entry.clone());
        }

        let pos = self
            .entries_sorted_addr
            .binary_search_by(|probe| probe.addr().cmp(&address));
        let entry = match pos {
            Ok(idx) => Some(self.entries_sorted_addr[idx].clone()),
            Err(idx) => {
                if idx == 0 {
                    None
                } else {
                    Some(self.entries_sorted_addr[idx - 1].clone())
                }
            }
        };

        if let Some(entry) = entry {
            self.entry_for_address_cache.insert(address, entry.clone());
            Some(entry)
        } else {
            None
        }
    }
}
