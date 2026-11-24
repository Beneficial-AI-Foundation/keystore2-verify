import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open permission.perm
open permission.KeyPermSet.Insts
open permission.perm.IntoIter.Insts
open CoreIterTraitsIteratorIteratorKeyPerm renaming next → iterNext
open permission.KeyPerm.Insts.CoreConvertFromI32 renaming «from» → keyPermFromI32

/-- exact: `IntoIter::new` never fails. It returns the iterator over the set, at position 0. -/
theorem into_iter_new (v : permission.KeyPermSet) :
    IntoIter.new v = ok { vec := v, pos := 0#u8 } := by
  sorry

/-- exact: `KeyPermSet::into_iter` never fails. It returns the iterator over the set, at
position 0. -/
theorem key_perm_set_into_iter (v : permission.KeyPermSet) :
    CoreIterTraitsCollectIntoIteratorKeyPermIntoIter.into_iter v =
      ok { vec := v, pos := 0#u8 } := by
  sorry

/-- exact: if some bit at position `pos` or above is set, `next` returns the permission of the
lowest such bit `i`, that is `KeyPerm::from(1 << i)`, and moves the position to `i + 1`. The set
does not change. A set bit that is no `KeyPerm` (bit 10, bits 12 to 31) gives `KeyPerm::None`,
and is not skipped. -/
theorem into_iter_next_some (it : permission.perm.IntoIter) (i : Nat)
    (hi : NextBit it.vec it.pos.val i) :
    ∃ kp it', keyPermFromI32 (bitVal i) = ok kp ∧ iterNext it = ok (some kp, it') ∧
      it'.vec = it.vec ∧ it'.pos.val = i + 1 := by
  sorry

/-- exact: if the position is at most 32 and no bit at position `pos` or above is set, `next`
returns `None` and moves the position to 32. The set does not change. With position 32 this says
that the iterator stays finished. -/
theorem into_iter_next_none (it : permission.perm.IntoIter) (hpos : it.pos.val ≤ 32)
    (hnone : ∀ j, it.pos.val ≤ j → j < 32 → ¬ HasBit it.vec j) :
    ∃ it', iterNext it = ok (none, it') ∧ it'.vec = it.vec ∧ it'.pos.val = 32 := by
  sorry

/-- exact: a position above 32 makes `next` panic, because the shift `1 << pos` is out of range.
Rust code cannot build such an iterator: the field `pos` is private and only `next` changes it,
so this is a fact about the Lean model only. -/
theorem into_iter_next_pos_too_large (it : permission.perm.IntoIter) (hpos : 32 < it.pos.val) :
    ∃ x, iterNext it = fail x := by
  sorry

end Keystore2Verify.Permission
