import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open error.Error.Insts.CoreConvertFromError renaming «from» → errorFromRkpd
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode

/-- conditional: `Error::from` maps `RequestCancelled`, `GetRegistrationFailed` and
`RetryableTimeout` to `Rc OUT_OF_KEYS_TRANSIENT_ERROR`. Hypothesis: the constant is `ok c`. -/
theorem Error_from_rkpd_transient (e : rkpd_client.Error) (c : Std.I32)
    (he : e = rkpd_client.Error.RequestCancelled ∨ e = rkpd_client.Error.GetRegistrationFailed ∨
      e = rkpd_client.Error.RetryableTimeout)
    (hc : ResponseCode.OUT_OF_KEYS_TRANSIENT_ERROR = ok c) :
    errorFromRkpd e = ok (error.Error.Rc c) := by
  sorry

/-- conditional: `Error::from` maps `GetKeyFailed ERROR_UNKNOWN` (1) to
`Rc OUT_OF_KEYS_TRANSIENT_ERROR`. Hypothesis: the constant is `ok c`. -/
theorem Error_from_rkpd_get_key_unknown (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_TRANSIENT_ERROR = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 1#i8) = ok (error.Error.Rc c) := by
  sorry

/-- conditional: `Error::from` maps `GetKeyFailed ERROR_PERMANENT` (5) to
`Rc OUT_OF_KEYS_PERMANENT_ERROR`. Hypothesis: the constant is `ok c`. -/
theorem Error_from_rkpd_get_key_permanent (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_PERMANENT_ERROR = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 5#i8) = ok (error.Error.Rc c) := by
  sorry

/-- conditional: `Error::from` maps `GetKeyFailed ERROR_PENDING_INTERNET_CONNECTIVITY` (3) to
`Rc OUT_OF_KEYS_PENDING_INTERNET_CONNECTIVITY`. Hypothesis: the constant is `ok c`. -/
theorem Error_from_rkpd_get_key_pending (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_PENDING_INTERNET_CONNECTIVITY = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 3#i8) = ok (error.Error.Rc c) := by
  sorry

/-- conditional: `Error::from` maps `GetKeyFailed ERROR_REQUIRES_SECURITY_PATCH` (2) to
`Rc OUT_OF_KEYS_REQUIRES_SYSTEM_UPGRADE`. Hypothesis: the constant is `ok c`. -/
theorem Error_from_rkpd_get_key_security_patch (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_REQUIRES_SYSTEM_UPGRADE = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 2#i8) = ok (error.Error.Rc c) := by
  sorry

/-- conditional: `Error::from` maps `GetKeyFailed` with any code other than 1, 2, 3 and 5 to
`Rc OUT_OF_KEYS_TRANSIENT_ERROR`. In the Rust source this path also logs the code at `Error`
level. Hypotheses: the constant is `ok c`, and the four assumptions about logging. -/
theorem Error_from_rkpd_get_key_other (g : Std.I8) (c : Std.I32)
    (h1 : g ≠ 1#i8) (h2 : g ≠ 2#i8) (h3 : g ≠ 3#i8) (h5 : g ≠ 5#i8)
    (hc : ResponseCode.OUT_OF_KEYS_TRANSIENT_ERROR = ok c)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed g) = ok (error.Error.Rc c) := by
  sorry

/-- exact: `Error::from` maps `StoreUpgradedKeyFailed` and `Timeout` to `Rc SYSTEM_ERROR`,
the code 4. -/
theorem Error_from_rkpd_system_error (e : rkpd_client.Error)
    (he : e = rkpd_client.Error.StoreUpgradedKeyFailed ∨ e = rkpd_client.Error.Timeout) :
    errorFromRkpd e = ok (error.Error.Rc 4#i32) := by
  sorry

/-- exact: `Error::from` maps `BinderTransaction s` to the `BinderTransaction` variant of
`Error` with the same status. -/
theorem Error_from_rkpd_binder_transaction (s : binder.StatusCode) :
    errorFromRkpd (rkpd_client.Error.BinderTransaction s) =
      ok (error.Error.BinderTransaction s) := by
  sorry

/-- conditional: `Error::from` maps `TooManyConcurrentOperations` to `Rc BACKEND_BUSY`.
Hypothesis: the constant is `ok c`. -/
theorem Error_from_rkpd_too_many_operations (c : Std.I32)
    (hc : ResponseCode.BACKEND_BUSY = ok c) :
    errorFromRkpd rkpd_client.Error.TooManyConcurrentOperations = ok (error.Error.Rc c) := by
  sorry

end Keystore2Verify.Error
