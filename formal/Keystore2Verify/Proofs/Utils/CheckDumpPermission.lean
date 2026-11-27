import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open android_system_keystore2.aidl.android.system.keystore2
open ResponseCode.ResponseCode renaming PERMISSION_DENIED → permissionDenied

/-- conditional: if the constant `ResponseCode::PERMISSION_DENIED` is `ok c` and
`check_android_permission` returns `Ok ()` for the permission `android.permission.DUMP` and the
error `Rc c`, then `check_dump_permission` returns `Ok ()`. Hypotheses: the outcome of the
constant (`hc`) and the outcome of the call (`hcall`). The extraction leaves
`check_android_permission` opaque, so when it returns `Ok` is not stated. -/
theorem check_dump_permission_ok (c : ResponseCode.ResponseCode)
    (hc : permissionDenied = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.DUMP") (error.Error.Rc c) = ok (ROk ())) :
    utils.check_dump_permission = ok (ROk ()) := by
  sorry

/-- conditional: if the constant `ResponseCode::PERMISSION_DENIED` is `ok c` and
`check_android_permission` returns `Err e` for the permission `android.permission.DUMP` and the
error `Rc c`, then `check_dump_permission` returns an `Err` with the same root cause as `e`, as
classified by `root`. Hypotheses: the outcome of the constant (`hc`) and the outcome of the call
(`hcall`). The extraction leaves `check_android_permission` opaque, so the root of `e` is not
stated. -/
theorem check_dump_permission_err
    (root : anyhow.Error → ErrRoot) (c : ResponseCode.ResponseCode) (e : anyhow.Error)
    (hc : permissionDenied = ok c)
    (hcall : utils.check_android_permission
      (toStr "android.permission.DUMP")
      (error.Error.Rc c) = ok (RErr e)) :
    ∃ e', utils.check_dump_permission = ok (RErr e') ∧
      root e' = root e := by
  sorry

end Keystore2Verify.Utils
