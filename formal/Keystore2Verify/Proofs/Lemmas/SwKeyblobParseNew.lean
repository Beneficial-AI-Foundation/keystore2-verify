import Keystore2Verify.Proofs.Lemmas.SwKeyblobParseHmac
import Keystore2Verify.Proofs.SwKeyblob.ConsumeU8
import Keystore2Verify.Proofs.SwKeyblob.ConsumeVec

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- A bind returns `ok b` exactly when its first part returns a value and the rest returns
`ok b`. -/
theorem bind_eq_ok_iff {α β : Type} (x : Result α) (f : α → Result β) (b : β) :
    Std.bind x f = ok b ↔ ∃ a, x = ok a ∧ f a = ok b := by
  rcases result_trichotomy x with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
  · simp
  · constructor
    · intro h
      simp at h
    · rintro ⟨a, ha, _⟩
      simp at ha
  · constructor
    · intro h
      simp at h
    · rintro ⟨a, ha, _⟩
      simp at ha

/-- The subtraction `data.len - 8` in `usize` when the slice has at least 8 bytes. -/
theorem len_sub8 (data : Slice Std.U8) (h : 8 ≤ data.val.length) :
    ∃ z, data.len - 8#usize = ok z ∧ z.val = data.val.length - 8 := by
  have hs := UScalar.sub_spec (x := data.len) (y := 8#usize) (by simp; omega)
  cases hx : data.len - 8#usize <;> rw [hx] at hs <;> simp_all

/-- The facts about the first steps of `new_from_serialized` on a blob of at least 21 bytes: the
size of `u32`, the offset `len - 8`, the two slices that the code takes, and the comparison of
the last 8 bytes with a MAC `m`. -/
theorem nfs_mac_facts (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8) :
    ∃ z b, core.mem.size_of Std.U32 = ok 4#usize ∧ data.len - 8#usize = ok z ∧
      z.val = data.val.length - 8 ∧
      (∀ pf, Slice.from (List.take z.val data.val) pf = s) ∧
      Shared0Slice.Insts.CoreCmpPartialEqVec.ne alloc.alloc.Global core.cmp.PartialEqU8
        (data.drop z) m = ok b ∧
      (b = true ↔ data.val.drop (data.val.length - 8) ≠ m.val) := by
  obtain ⟨n, hn, hn4⟩ := hsize
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  obtain ⟨z, hz, hzv⟩ := len_sub8 data (by unfold minBlobLen at h; omega)
  obtain ⟨b, hb, hbiff⟩ := hne (data.drop z) m
  refine ⟨z, b, by rw [hn, hn'], hz, hzv, ?_, hb, ?_⟩
  · intro pf
    exact Slice.ext _ _ (by simp [hs, hzv])
  · rw [hbiff]
    simp [Slice.drop, hzv]

/-- The facts about the steps of `new_from_serialized` up to the first call of
`deserialize_params`, when all checks before the parameter lists pass (`PastKey`). -/
theorem nfs_key_facts (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) :
    ∃ (z : Usize) (s : Slice Std.U8) (m : alloc.vec.Vec Std.U8) (data1 data2 : Slice Std.U8)
      (vec : alloc.vec.Vec Std.U8),
      core.mem.size_of Std.U32 = ok 4#usize ∧ data.len - 8#usize = ok z ∧
      z.val ≤ data.val.length ∧
      (∀ pf, Slice.from (List.take z.val data.val) pf = s) ∧
      sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m) ∧
      Shared0Slice.Insts.CoreCmpPartialEqVec.ne alloc.alloc.Global core.cmp.PartialEqU8
        (data.drop z) m = ok false ∧
      sw_keyblob.consume_u8 data = ok (.Ok 0#u8, data1) ∧ data1.val = data.val.drop 1 ∧
      sw_keyblob.consume_vec data1 = ok (.Ok vec, data2) ∧
      vec.val = (data.val.drop 5).take (u32At data.val 1) ∧
      data2.val = data.val.drop (5 + u32At data.val 1) := by
  obtain ⟨⟨hlen, s, m, hs, hmac, hdrop⟩, hv, hle⟩ := hpast
  obtain ⟨z, b, hn, hz, hzv, key, hb, hbiff⟩ := nfs_mac_facts hsize hne data hlen s hs m
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd hdrop (hbiff.1 rfl)
  subst hbf
  obtain ⟨rest, hr⟩ : ∃ rest, data.val = 0#u8 :: rest := by
    cases hd : data.val <;> simp_all
  obtain ⟨data1, hc8, hd1⟩ := consume_u8_ok hfirst data 0#u8 rest hr
  have hd1' : data1.val = data.val.drop 1 := by rw [hd1, hr]; rfl
  have hlen' : 21 ≤ data.val.length := hlen
  have hu : u32At data1.val 0 = u32At data.val 1 := by simp [hd1', u32At]
  obtain ⟨vec, data2, hcv, hvv, hd2⟩ := consume_vec_ok hsize hfrom data1
    (by rw [hd1']; simp; omega) (by rw [hu, hd1']; simp; omega)
  refine ⟨z, s, m, data1, data2, vec, hn, hz, by omega, key, hmac, hb, hc8, hd1', hcv, ?_, ?_⟩
  · rw [hvv, hu, hd1']; simp [Nat.add_comm]
  · rw [hd2, hu, hd1']; simp; congr 1; omega

/-- If the length prefix is larger than the bytes after it, `consume_vec` never returns `Ok`,
whatever the error laws are. -/
theorem consume_vec_big (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length)
    (hbig : data.val.length - 4 < u32At data.val 0) (r : core.result.Result (alloc.vec.Vec Std.U8)
      anyhow.Error) (d' : Slice Std.U8) (hr : sw_keyblob.consume_vec data = ok (r, d')) :
    ∃ e, r = .Err e := by
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data h
  have hlt : data1.val.length < x.val := by
    rw [hxv, hd1]; simp; omega
  unfold sw_keyblob.consume_vec at hr
  simp [hx, core.result.Result.Insts.CoreOpsTry.branch, lift, hlt, bind_eq_ok_iff] at hr
  obtain ⟨_, -, _, -, _, -, a, -, hra, -⟩ := hr
  exact ⟨a, hra.symm⟩

end Keystore2Verify.SwKeyblob
