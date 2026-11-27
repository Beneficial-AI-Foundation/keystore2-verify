import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → rOk, Err → rErr

/-- exact: `map_binder_status_code` keeps an `Ok` value unchanged. -/
theorem map_binder_status_code_ok {T : Type} (t : T) :
    error.map_binder_status_code
      (rOk t : core.result.Result T binder.StatusCode) =
      ok (rOk t) := by
  sorry

/-- exact: `map_binder_status_code` turns an `Err s` into an `Err` of the `BinderTransaction`
variant that wraps `s`. -/
theorem map_binder_status_code_err {T : Type} (s : binder.StatusCode) :
    error.map_binder_status_code
      (rErr s : core.result.Result T binder.StatusCode) =
      ok (rErr (error.Error.BinderTransaction s)) := by
  sorry

end Keystore2Verify.Error
