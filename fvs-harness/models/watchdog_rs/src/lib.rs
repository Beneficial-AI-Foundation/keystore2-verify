//! Model of `keystore2/watchdog` (crate `watchdog_rs`): the same public API, no body. keystore2 uses it
//! when its `watchdog` feature is on, as Soong builds it (`keystore2/Android.bp`). The upstream crate
//! runs a thread that logs watch points that stay armed past their deadline; logging is all it does
//! with them. Every function is an oracle and every type is opaque.
#![feature(register_tool)]
#![register_tool(charon)]

use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Duration;

/// An armed watch point. Dropping it disarms it. Like the upstream type, it is neither `Send` nor
/// `Sync`.
#[charon::opaque]
pub struct WatchPoint {
    _not_send: PhantomData<*mut ()>,
}

impl Drop for WatchPoint {
    #[charon::opaque]
    fn drop(&mut self) {
        unimplemented!("model: disarm a watch point")
    }
}

/// A watchdog. Upstream it holds the watchdog thread's shared state; it is `Send` and `Sync`.
#[charon::opaque]
pub struct Watchdog {
    _state: (),
}

impl Watchdog {
    /// A new watchdog whose thread stops after `idle_timeout` with no armed watch point.
    #[charon::opaque]
    pub fn new(_idle_timeout: Duration) -> Arc<Self> {
        unimplemented!("model: Watchdog::new")
    }

    /// Arms a watch point with a context that is logged with each report. `None` when the deadline
    /// cannot be computed.
    #[charon::opaque]
    pub fn watch_with(
        _wd: &Arc<Self>,
        _id: &'static str,
        _timeout: Duration,
        _context: impl std::fmt::Debug + Send + 'static,
    ) -> Option<WatchPoint> {
        unimplemented!("model: Watchdog::watch_with")
    }

    /// Arms a watch point. `None` when the deadline cannot be computed.
    #[charon::opaque]
    pub fn watch(_wd: &Arc<Self>, _id: &'static str, _timeout: Duration) -> Option<WatchPoint> {
        unimplemented!("model: Watchdog::watch")
    }
}
