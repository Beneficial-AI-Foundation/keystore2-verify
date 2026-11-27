import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open utils.SecureUserId.Insts
open CoreCmpPartialEqSecureUserId renaming eq → secureUserIdEq
open CoreCloneClone renaming clone → secureUserIdClone
open CoreCmpOrd renaming cmp → secureUserIdCmp
open CoreCmpPartialOrdSecureUserId renaming partial_cmp → secureUserIdPartialCmp

/-- exact: `SecureUserId::eq` never fails and returns `true` exactly when the two numbers
are equal. -/
theorem secureUserId_eq (x y : utils.SecureUserId) :
    secureUserIdEq x y = ok (decide (x = y)) := by
  sorry

/-- exact: `SecureUserId::clone` never fails and returns its argument. -/
theorem secureUserId_clone (x : utils.SecureUserId) : secureUserIdClone x = ok x := by
  sorry

/-- exact: `SecureUserId::cmp` never fails. It compares the two numbers as signed integers. -/
theorem secureUserId_cmp (x y : utils.SecureUserId) :
    secureUserIdCmp x y = ok (compare x.val y.val) := by
  sorry

/-- exact: `SecureUserId::partial_cmp` never fails and returns `Some` of the signed comparison of
the two numbers. -/
theorem secureUserId_partial_cmp (x y : utils.SecureUserId) :
    secureUserIdPartialCmp x y = ok (some (compare x.val y.val)) := by
  sorry

end Keystore2Verify.Utils
