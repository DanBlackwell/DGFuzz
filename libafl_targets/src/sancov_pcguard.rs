//! [`LLVM` `PcGuard`](https://clang.llvm.org/docs/SanitizerCoverage.html#tracing-pcs-with-guards) runtime for `LibAFL`.

use crate::coverage::{EDGES_MAP, MAX_EDGES_NUM};
#[cfg(feature = "pointer_maps")]
use crate::coverage::{EDGES_MAP_PTR, EDGES_MAP_PTR_NUM};

#[cfg(all(feature = "sancov_pcguard_edges", feature = "sancov_pcguard_hitcounts"))]
#[cfg(not(any(doc, feature = "clippy")))]
compile_error!(
    "the libafl_targets `sancov_pcguard_edges` and `sancov_pcguard_hitcounts` features are mutually exclusive."
);

use std::collections::HashSet;
use once_cell::unsync::Lazy;
static mut SEEN_GUARDS: Lazy<HashSet<u32>> = Lazy::new(|| HashSet::new());
static mut UNUSED_GUARD_INDEXES: Lazy<HashSet<u32>> = Lazy::new(|| HashSet::new());

/// Callback for sancov `pc_guard` - usually called by `llvm` on each block or edge.
///
/// # Safety
/// Dereferences `guard`, reads the position from there, then dereferences the [`EDGES_MAP`] at that position.
/// Should usually not be called directly.
#[no_mangle]
pub unsafe extern "C" fn __sanitizer_cov_trace_pc_guard(guard: *mut u32) {
    let pos = *guard as usize;
    //if !seen_guards.contains(&(pos as u32)) {
    //    panic!("ERROR: saw a guard {pos} that was not seen in the init???");
    //}
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
        EDGES_MAP_PTR_NUM = EDGES_MAP.len();
    }

    if start == stop { //|| *start != 0 {
        return;
    }

    let mut seen = vec![];
    let mut set_seen = HashSet::new();
    let mut dupes = vec![];
    while start < stop {
        seen.push(*start);
        SEEN_GUARDS.insert(*start);
        if !set_seen.insert(*start) {
           dupes.push(*start); 
        }
        start = start.offset(1);
    }

    let max = seen.iter().fold(0, |max, &x| if x > max { x } else { max });
    MAX_EDGES_NUM = max as usize + 1;
    for i in 0..=max {
        if !set_seen.contains(&i) { 
            UNUSED_GUARD_INDEXES.insert(i);
        }
    }
    // std::fs::write("debug.info", format!("all: {:?},\ndupes:{:?},\nunseen: {:?}", seen, dupes, unused_guard_indexes).as_bytes());
}
