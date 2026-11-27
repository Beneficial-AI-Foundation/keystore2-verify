import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open utils.AndroidUserId.Insts
open CoreCmpPartialEqAndroidUserId renaming eq → androidUserIdEq
open CoreCloneClone renaming clone → androidUserIdClone
open CoreCmpOrd renaming cmp → androidUserIdCmp
open CoreCmpPartialOrdAndroidUserId renaming partial_cmp → androidUserIdPartialCmp

/-- exact: `AndroidUserId::eq` never fails and returns `true` exactly when the two numbers
are equal. -/
theorem androidUserId_eq (x y : utils.AndroidUserId) :
    androidUserIdEq x y = ok (decide (x = y)) := by
  sorry

/-- exact: `AndroidUserId::clone` never fails and returns its argument. -/
theorem androidUserId_clone (x : utils.AndroidUserId) : androidUserIdClone x = ok x := by
  sorry

/-- exact: `AndroidUserId::cmp` never fails. It compares the two numbers as signed integers. -/
theorem androidUserId_cmp (x y : utils.AndroidUserId) :
    androidUserIdCmp x y = ok (compare x.val y.val) := by
  sorry

/-- exact: `AndroidUserId::partial_cmp` never fails and returns `Some` of the signed comparison of
the two numbers. -/
theorem androidUserId_partial_cmp (x y : utils.AndroidUserId) :
    androidUserIdPartialCmp x y = ok (some (compare x.val y.val)) := by
  sorry

end Keystore2Verify.Utils
