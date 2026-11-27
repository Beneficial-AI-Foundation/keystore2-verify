import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open ErrorCode.ErrorCode renaming CANNOT_ATTEST_IDS → cannotAttestIds

/-- conditional: if the constant `ErrorCode::CANNOT_ATTEST_IDS` is `ok c` and
`check_android_permission` returns `Ok ()` for the permission
`android.permission.REQUEST_UNIQUE_ID_ATTESTATION` and the error `Km c`, then
`check_unique_id_attestation_permissions` returns `Ok ()`. Hypotheses: the outcome of the constant
(`hc`) and the outcome of the call (`hcall`). The extraction leaves `check_android_permission`
opaque, so when it returns `Ok` is not stated. -/
theorem check_unique_id_attestation_permissions_ok (c : ErrorCode.ErrorCode)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.REQUEST_UNIQUE_ID_ATTESTATION") (error.Error.Km c) = ok (ROk ())) :
    utils.check_unique_id_attestation_permissions = ok (ROk ()) := by
  sorry

/-- conditional: if the constant `ErrorCode::CANNOT_ATTEST_IDS` is `ok c` and
`check_android_permission` returns `Err e` for the permission
`android.permission.REQUEST_UNIQUE_ID_ATTESTATION` and the error `Km c`, then
`check_unique_id_attestation_permissions` returns an `Err` with the same root cause as `e`, as
classified by `root`. Hypotheses: the outcome of the constant (`hc`) and the outcome of the call
(`hcall`). The extraction leaves `check_android_permission` opaque, so the root of `e` is not
stated. -/
theorem check_unique_id_attestation_permissions_err
    (root : anyhow.Error → ErrRoot) (c : ErrorCode.ErrorCode) (e : anyhow.Error)
    (hc : cannotAttestIds = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.REQUEST_UNIQUE_ID_ATTESTATION")
      (error.Error.Km c) = ok (RErr e)) :
    ∃ e', utils.check_unique_id_attestation_permissions = ok (RErr e') ∧
      root e' = root e := by
  sorry

end Keystore2Verify.Utils
