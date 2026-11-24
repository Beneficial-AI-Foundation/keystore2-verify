//! Stand-in for the Android `structured_log` crate (security audit log).
//!
//! `structured_log!` evaluates its arguments and discards them. The log id constant is not
//! load-bearing.

pub const LOG_ID_SECURITY: u32 = 6;

#[macro_export]
macro_rules! structured_log {
    (log_id: $log_id:expr, $tag:expr $(, $arg:expr)* $(,)?) => {{
        let _ = ($log_id, $tag $(, &$arg)*);
    }};
}
