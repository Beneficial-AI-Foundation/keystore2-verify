import Keystore2Verify.Proofs.Lemmas.SwKeyblobReaders

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- Building `data ++ hd` in a vector succeeds when the sum fits in the vector model. -/
theorem hmac_combine_ok (data : Slice Std.U8) (hd : alloc.vec.Vec Std.U8)
    (h : data.val.length + hd.val.length ≤ Std.Usize.max) :
    ∃ v c, alloc.slice.Slice.to_vec core.clone.CloneU8 data = ok v ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v (alloc.vec.Vec.deref hd) = ok c ∧
      c.val = data.val ++ hd.val := by
  obtain ⟨v, hv, hvv⟩ := to_vec_u8 data
  have hl : v.length + (alloc.vec.Vec.deref hd).length ≤ Std.Usize.max := by
    have hdv : (alloc.vec.Vec.deref hd).val = hd.val := by simp [alloc.vec.Vec.deref]
    simp only [alloc.vec.Vec.length, Slice.length, hdv, hvv]
    exact h
  have hc : (v.val ++ hd.val).length ≤ Std.Usize.max := by
    rw [List.length_append, hvv]; exact h
  refine ⟨v, alloc.vec.Vec.from (v.val ++ hd.val) hc, hv, ?_, by simp [hvv]⟩
  have hdv : (alloc.vec.Vec.deref hd).val = hd.val := by simp [alloc.vec.Vec.deref]
  obtain ⟨l', hl', hl'v⟩ : ∃ l', List.clone core.clone.CloneU8.clone
      (alloc.vec.Vec.deref hd).val = ok l' ∧ l'.val = hd.val := by
    have hs := List.clone_spec (clone := core.clone.CloneU8.clone)
      (l := (alloc.vec.Vec.deref hd).val) (fun _ _ => rfl)
    cases hx : List.clone core.clone.CloneU8.clone (alloc.vec.Vec.deref hd).val <;>
      rw [hx] at hs <;> simp_all
  unfold alloc.vec.Vec.extend_from_slice
  simp only [hl, ↓reduceDIte, hl', bind_tc_ok, hl'v]

/-- A result is a value, a failure or a divergence. -/
theorem result_trichotomy {α : Type} (r : Result α) :
    (∃ a, r = ok a) ∨ (∃ x, r = fail x) ∨ r = div := by
  induction r using Result.cases with
  | ret a => exact Or.inl ⟨a, rfl⟩
  | vis i k =>
    cases i with
    | fail x =>
      refine Or.inr (Or.inl ⟨x, ?_⟩)
      rw [Result.fail_eq_vis]
      show Result.vis _ k = Result.vis _ _
      congr
      funext e; cases e
  | div => exact Or.inr (Or.inr rfl)

/-- The three `usize` operations that give the length threshold of `new_from_serialized`. -/
theorem nfs_consts : (3#usize * 4#usize = ok 12#usize) ∧ (1#usize + 12#usize = ok 13#usize) ∧
    (13#usize + 8#usize = ok 21#usize) := by
  have hm := UScalar.mul_spec (x := 3#usize) (y := 4#usize) (by scalar_tac)
  have h1 := usize_add_ok 1#usize 12#usize (by scalar_tac)
  have h2 := usize_add_ok 13#usize 8#usize (by scalar_tac)
  obtain ⟨z1, hz1, hv1⟩ := h1
  obtain ⟨z2, hz2, hv2⟩ := h2
  have e1 : z1 = 13#usize := UScalar.eq_of_val_eq (by simpa using hv1)
  have e2 : z2 = 21#usize := UScalar.eq_of_val_eq (by simpa using hv2)
  refine ⟨?_, by rw [hz1, e1], by rw [hz2, e2]⟩
  cases hx : 3#usize * 4#usize <;> rw [hx] at hm <;> simp_all
  exact UScalar.eq_of_val_eq (by simpa using hm)

/-- The constant `MAC_LEN` is 8. -/
theorem mac_len_eq : sw_keyblob.KeyBlob.MAC_LEN = 8#usize := by
  unfold sw_keyblob.KeyBlob.MAC_LEN; rfl

/-- The constant `KEY_BLOB_VERSION` is 0. -/
theorem key_blob_version_eq : sw_keyblob.KeyBlob.KEY_BLOB_VERSION = 0#u8 := by
  unfold sw_keyblob.KeyBlob.KEY_BLOB_VERSION; rfl

end Keystore2Verify.SwKeyblob
