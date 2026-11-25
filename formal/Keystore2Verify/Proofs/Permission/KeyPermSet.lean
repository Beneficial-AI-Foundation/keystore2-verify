import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open I32.Insts.CoreConvertFromKeyPermSet renaming «from» → i32FromKeyPermSet
open permission.KeyPermSet.Insts
open CoreConvertFromKeyPerm renaming «from» → setFromKeyPerm
open CoreConvertFromI32 renaming «from» → setFromI32
open CoreCloneClone renaming clone → setClone
open CoreCmpPartialEqKeyPermSet renaming eq → setEq
open CoreCmpOrd renaming cmp → setCmp
open CoreCmpPartialOrdKeyPermSet renaming partial_cmp → setPartialCmp

/-- exact: `KeyPermSet::from(KeyPerm)` never fails. The set is the number of the permission
(`keyPermValue`), so `None` gives the empty set and every other variant gives one bit. -/
theorem key_perm_set_from_key_perm (p : permission.KeyPerm) :
    ∃ s, setFromKeyPerm p = ok s ∧ s.val = keyPermValue p := by
  sorry

/-- exact: `KeyPermSet::from(i32)` never fails and keeps every bit, the bits that are no `KeyPerm`
included. -/
theorem key_perm_set_from_i32 (x : Std.I32) : setFromI32 x = ok x := by
  sorry

/-- exact: `i32::from(KeyPermSet)` never fails and returns the number of the set unchanged. -/
theorem i32_from_key_perm_set (s : permission.KeyPermSet) :
    i32FromKeyPermSet s = ok s := by
  sorry

/-- exact: `clone` returns the same set. -/
theorem key_perm_set_clone (s : permission.KeyPermSet) : setClone s = ok s := by
  sorry

/-- exact: `eq` never fails and is `true` exactly when the two numbers are equal. -/
theorem key_perm_set_eq (a b : permission.KeyPermSet) :
    ∃ r, setEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails and compares the numbers as signed `i32` values. It is not the
inclusion of sets: for example the set with every bit (the number -1) is less than the empty
set. -/
theorem key_perm_set_cmp (a b : permission.KeyPermSet) :
    setCmp a b = ok (compare a.val b.val) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem key_perm_set_partial_cmp (a b : permission.KeyPermSet) :
    setPartialCmp a b = ok (some (compare a.val b.val)) := by
  sorry

end Keystore2Verify.Permission
