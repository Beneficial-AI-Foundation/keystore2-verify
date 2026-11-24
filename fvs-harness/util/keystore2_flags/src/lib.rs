//! Stand-in for the generated `keystore2_flags` crate (aconfig flags).
//!
//! The six flags keystore2 reads. Each value is opaque: the functions are marked
//! `#[charon::opaque]`, so no flag is fixed to its production value.
#![feature(register_tool)]
#![register_tool(charon)]

#[charon::opaque]
pub fn async_lock_state() -> bool {
    unimplemented!("stand-in: aconfig flag async_lock_state")
}

#[charon::opaque]
pub fn atoms_v2() -> bool {
    unimplemented!("stand-in: aconfig flag atoms_v2")
}

#[charon::opaque]
pub fn faster_rebind_cleanup() -> bool {
    unimplemented!("stand-in: aconfig flag faster_rebind_cleanup")
}

#[charon::opaque]
pub fn import_previously_emulated_keys() -> bool {
    unimplemented!("stand-in: aconfig flag import_previously_emulated_keys")
}

#[charon::opaque]
pub fn limit_keys_per_uid() -> bool {
    unimplemented!("stand-in: aconfig flag limit_keys_per_uid")
}

#[charon::opaque]
pub fn renice_async_task() -> bool {
    unimplemented!("stand-in: aconfig flag renice_async_task")
}
