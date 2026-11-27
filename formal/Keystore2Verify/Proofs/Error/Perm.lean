import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode

/-- conditional: `Error::perm()` returns `Error::Rc` that wraps the value of the constant
`ResponseCode::PERMISSION_DENIED`. Hypothesis: the constant is `ok c`. -/
theorem Error_perm (c : Std.I32) (hc : ResponseCode.PERMISSION_DENIED = ok c) :
    error.Error.perm = ok (error.Error.Rc c) := by
  sorry

end Keystore2Verify.Error
