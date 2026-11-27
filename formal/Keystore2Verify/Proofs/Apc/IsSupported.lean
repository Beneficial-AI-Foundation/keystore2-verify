import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.Apc
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_security_apc.aidl.android.security.apc
open keystore2.std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault
  renaming default → hashMapDefault
open keystore2.core.time.Duration
  renaming from_secs → durationFromSecs, checked_sub → durationCheckedSub,
    checked_mul → durationCheckedMul
open keystore2.std.time.Instant renaming elapsed → instantElapsed
open Aeneas.Std.core.option.Option renaming unwrap_or → optionUnwrapOr
open keystore2.std.sync.mpsc (Sender)
open keystore2.std.collections.hash.map (HashMap)
open keystore2.std.hash.random (RandomState)
open keystore2.std.hash.random.RandomState.Insts renaming CoreDefaultDefault → randomStateDefault

/-- conditional: if `ApcHal::try_get_service` returns `o`, then `is_supported` returns `Ok b`, where
`b` is `true` exactly when a service was found. Hypothesis: the outcome of `try_get_service`. -/
theorem apc_manager_is_supported_ok (o : Option keystore2_apc_compat.ApcHal)
    (h : keystore2_apc_compat.ApcHal.try_get_service = ok o) :
    ∃ b, apc.ApcManager.is_supported = ok (.Ok b) ∧ (b = true ↔ o ≠ none) := by
  sorry

/-- conditional: if `ApcHal::try_get_service` fails with `x`, `is_supported` fails with `x`.
Hypothesis: the outcome of `try_get_service`. -/
theorem apc_manager_is_supported_fail (x : Error)
    (h : keystore2_apc_compat.ApcHal.try_get_service = fail x) :
    apc.ApcManager.is_supported = fail x := by
  sorry

end Keystore2Verify.Apc
