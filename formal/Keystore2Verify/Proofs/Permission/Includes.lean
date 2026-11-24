import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open permission.KeyPermSet.Insts

/-- conditional: for any type `T` with a conversion into `KeyPermSet`, if the conversion of
`other` returns `o`, then `includes` returns `true` exactly when `self` contains every bit of `o`.
Hypothesis: the outcome of the conversion `inst.into other`. -/
theorem includes_ok {T : Type} (inst : core.convert.Into T permission.KeyPermSet)
    (self : permission.KeyPermSet) (other : T) (o : permission.KeyPermSet)
    (h : inst.into other = ok o) :
    ∃ b, permission.KeyPermSet.includes inst self other = ok b ∧
      (b = true ↔ Includes self o) := by
  sorry

/-- exact: `includes` with a `KeyPerm` never fails. It is `true` exactly when the set contains
every bit of the bit set of the permission. For `KeyPerm::None` that set is empty, so the result
is `true`. -/
theorem includes_key_perm (self : permission.KeyPermSet) (p : permission.KeyPerm) :
    ∃ o b, CoreConvertFromKeyPerm.from p = ok o ∧
      permission.KeyPermSet.includes
        (core.convert.IntoFrom CoreConvertFromKeyPerm) self p = ok b ∧
      (b = true ↔ Includes self o) := by
  sorry

/-- exact: `includes` with an `i32` never fails. It is `true` exactly when `self` contains every
bit of the number. Bits that are no `KeyPerm`, and the sign bit, count like any other bit. -/
theorem includes_i32 (self : permission.KeyPermSet) (x : Std.I32) :
    ∃ b, permission.KeyPermSet.includes
        (core.convert.IntoFrom CoreConvertFromI32) self x = ok b ∧
      (b = true ↔ Includes self x) := by
  sorry

/-- exact: `includes` with a `KeyPermSet` never fails. It is `true` exactly when `self` contains
every bit of `other`. -/
theorem includes_key_perm_set (self other : permission.KeyPermSet) :
    ∃ b, permission.KeyPermSet.includes
        (core.convert.IntoFrom (core.convert.FromSame permission.KeyPermSet)) self other = ok b ∧
      (b = true ↔ Includes self other) := by
  sorry

end Keystore2Verify.Permission
