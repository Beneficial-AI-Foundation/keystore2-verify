import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

open rustutils.android.system_properties

/-! The root cause of a property watcher error is not a class that the model knows
(`ErrRoot.other`). The context texts of the Rust source are
`keystore2/src/globals.rs:486: PropertyWatcher::new failed` and
`keystore2/src/globals.rs:487: Failed to wait for sys.boot_completed`. -/

/-- conditional: if `PropertyWatcher::new("sys.boot_completed")` returns a watcher `w` and
`w.wait_for_value("1", None)` returns `Ok(())`, the function returns `Ok(())`. Hypotheses: the
outcomes of the two calls, the assumptions for `format` and `from_str_nonconst`, and the assumptions
for `Result::context` at the two calls. -/
theorem watch_for_boot_completed_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx1 : WatcherCtxSpec root PropertyWatcher) (hctx2 : WatcherCtxSpec root Unit)
    (w w' : PropertyWatcher)
    (hnew : PropertyWatcher.new (toStr "sys.boot_completed") = ok (.Ok w))
    (hwait : PropertyWatcher.wait_for_value w (toStr "1") none = ok (.Ok (), w')) :
    globals.watch_for_boot_completed = ok (.Ok ()) := by
  sorry

/-- conditional: if `PropertyWatcher::new("sys.boot_completed")` returns an error, the function
returns an error. In the Rust source this path returns before `wait_for_value` is called.
Hypotheses: the outcome of `new`, the assumptions for `format` and `from_str_nonconst`, and the
assumption for `Result::context` at the first call. -/
theorem watch_for_boot_completed_new_error (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx1 : WatcherCtxSpec root PropertyWatcher) (e : PropertyWatcherError)
    (hnew : PropertyWatcher.new (toStr "sys.boot_completed") = ok (.Err e)) :
    ∃ e', globals.watch_for_boot_completed = ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

/-- conditional: if `PropertyWatcher::new("sys.boot_completed")` returns a watcher `w` and
`w.wait_for_value("1", None)` returns an error, the function returns an error. Hypotheses: the
outcomes of the two calls, the assumptions for `format` and `from_str_nonconst`, and the assumptions
for `Result::context` at the two calls. -/
theorem watch_for_boot_completed_wait_error (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx1 : WatcherCtxSpec root PropertyWatcher) (hctx2 : WatcherCtxSpec root Unit)
    (w w' : PropertyWatcher) (e : PropertyWatcherError)
    (hnew : PropertyWatcher.new (toStr "sys.boot_completed") = ok (.Ok w))
    (hwait : PropertyWatcher.wait_for_value w (toStr "1") none = ok (.Err e, w')) :
    ∃ e', globals.watch_for_boot_completed = ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

end Keystore2Verify.Globals
