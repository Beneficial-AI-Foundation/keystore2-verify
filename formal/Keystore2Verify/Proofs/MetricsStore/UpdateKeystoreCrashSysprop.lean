import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open alloc.string.ToString.Blanket renaming to_string → toStringBlanket
open alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open rustutils.android.system_properties renaming
  write → writeProperty, PropertyWatcherError → PropWatchErr

/-- conditional: if the read of the property returns `Ok o`, the new count `crashCountNext o` is
`n` (the stored count plus one, or 0 if the property is absent), its text is `s`, the string slice
of `s` is `s1`, and the write of `s1` to `keystore.crash_count` returns `Ok`, then
`update_keystore_crash_sysprop` returns `()`. Hypotheses: the outcomes of the read, of the
increment, of `to_string` and `deref` on the text, and of the write. -/
theorem update_keystore_crash_sysprop_written (o : Option Std.I32) (n : Std.I32)
    (s : String) (s1 : Str)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk o))
    (hn : crashCountNext o = ok n)
    (hs : toStringBlanket I32.Insts.CoreFmtDisplay n = ok s)
    (hd : stringDeref s = ok s1)
    (hw : writeProperty metrics_store.KEYSTORE_CRASH_COUNT_PROPERTY s1 = ok (ROk ())) :
    metrics_store.update_keystore_crash_sysprop = ok () := by
  sorry

/-- conditional: the same as `update_keystore_crash_sysprop_written`, but the write returns an
error `e`. The function returns `()`. In the Rust source this path logs the error, if the log
level allows it. Hypotheses: those of `update_keystore_crash_sysprop_written` with the failed
write, and the shared assumptions about the log calls (`max_level`, the `Level` comparison,
`loc`, `log`). -/
theorem update_keystore_crash_sysprop_write_failed
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (o : Option Std.I32) (n : Std.I32) (s : String) (s1 : Str)
    (e : PropWatchErr)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk o))
    (hn : crashCountNext o = ok n)
    (hs : toStringBlanket I32.Insts.CoreFmtDisplay n = ok s)
    (hd : stringDeref s = ok s1)
    (hw : writeProperty metrics_store.KEYSTORE_CRASH_COUNT_PROPERTY s1 =
      ok (RErr e : core.result.Result Unit PropWatchErr)) :
    metrics_store.update_keystore_crash_sysprop = ok () := by
  sorry

/-- conditional: if the read of the property returns an error, the function returns `()`. In the
Rust source this path logs a warning, if the log level allows it, and returns before the
property is written. Hypotheses: the outcome of the read, and the shared assumptions about the
log calls. -/
theorem update_keystore_crash_sysprop_read_failed
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (e : anyhow.Error)
    (hrd : metrics_store.read_keystore_crash_count = ok (RErr e)) :
    metrics_store.update_keystore_crash_sysprop = ok () := by
  sorry

/-- conditional: if the read returns `Ok (some c)` with `c = i32::MAX`, the increment overflows
and the function fails with an integer overflow. In the Rust source this path returns before the
property is written. Hypothesis: the outcome of the read. -/
theorem update_keystore_crash_sysprop_overflow (c : Std.I32) (hc : c.val = 2 ^ 31 - 1)
    (hrd : metrics_store.read_keystore_crash_count = ok (ROk (some c))) :
    metrics_store.update_keystore_crash_sysprop = fail Error.integerOverflow := by
  sorry

end Keystore2Verify.MetricsStore
