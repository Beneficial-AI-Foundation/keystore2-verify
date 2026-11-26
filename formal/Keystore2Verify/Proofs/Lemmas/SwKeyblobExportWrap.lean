import Keystore2Verify.Proofs.Lemmas.SwKeyblobExportParse
import Keystore2Verify.Proofs.SwKeyblob.AddDerLen
import Keystore2Verify.Proofs.Lemmas.SwKeyblobWrap

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- A bind that returns `ok b` has a first step that returned `ok a`. -/
theorem bind_eq_ok_inv {A B : Type} (x : Result A) (k : A → Result B) (b : B)
    (h : Std.bind x k = ok b) : ∃ a, x = ok a ∧ k a = ok b := by
  cases x with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis i k' => simp at h
  | div => simp at h

/-- For a length above `0xffff`, `add_der_len` never returns `Ok`, whatever the laws. -/
theorem add_der_len_big (buf : alloc.vec.Vec Std.U8) (len : Std.Usize) (hlen : 0xffff < len.val)
    (r : core.result.Result Unit anyhow.Error) (b : alloc.vec.Vec Std.U8)
    (h : sw_keyblob.add_der_len buf len = ok (r, b)) : ∃ e, r = .Err e := by
  have h1 : ¬ len.val ≤ 127 := by omega
  have h2 : ¬ len.val ≤ 255 := by omega
  have h3 : ¬ len.val ≤ 65535 := by omega
  unfold sw_keyblob.add_der_len at h
  simp [h1, h2, h3, core.hint.must_use] at h
  obtain ⟨e0, -, h⟩ := bind_eq_ok_inv _ _ _ h
  obtain ⟨s0, -, h⟩ := bind_eq_ok_inv _ _ _ h
  obtain ⟨e1, -, h⟩ := bind_eq_ok_inv _ _ _ h
  simp at h
  exact ⟨e1, h.1.symm⟩


/-- If the body of the wrapper returns `Ok`, the content fits a DER length. -/
theorem wrap_body_ok_inv (alg key : Slice Std.U8) (halg : alg.val.length ≤ 0xffff)
    (out : alloc.vec.Vec Std.U8) (h : wrapBody alg key = ok (.Ok out)) :
    (pkcs8Body (nums alg.val) (nums key.val)).length ≤ 0xffff := by
  by_contra hbig
  have hmax : 4294967295 ≤ Std.Usize.max := by scalar_tac
  have hd3 := derLen_length_le key.val.length
  have hbl : (pkcs8Body (nums alg.val) (nums key.val)).length =
      3 + alg.val.length + (1 + (derLen key.val.length).length + key.val.length) := by
    simp [pkcs8Body, nums]; omega
  obtain ⟨n0, h0, hv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 4#u8
    (by simp [alloc.vec.Vec.new]; omega)
  by_cases hk : key.val.length ≤ 0xffff
  · obtain ⟨n1, h1, hv1⟩ := add_der_len_ok n0 (Slice.len key) (by simpa using hk)
      (by rw [hv0]; simp [alloc.vec.Vec.new]; omega)
    obtain ⟨n2, h2, hv2⟩ := extend_ok_aux n1 key (by
      have := congrArg List.length hv1
      simp [nums, hv0, alloc.vec.Vec.new] at this ⊢; omega)
    obtain ⟨b0, hb0, hbv0⟩ := push_ok_aux (alloc.vec.Vec.new Std.U8) 48#u8
      (by simp [alloc.vec.Vec.new]; omega)
    have hl2 : n2.val.length = 1 + (derLen key.val.length).length + key.val.length := by
      have := congrArg List.length hv1
      simp [nums, hv0, alloc.vec.Vec.new] at this
      rw [hv2]; simp [this]; omega
    obtain ⟨i3, hi3, hi3v⟩ := usize_add_ok (Slice.len sw_keyblob.DER_VERSION_0) (Slice.len alg)
      (by simp [der_version_val]; omega)
    obtain ⟨i5, hi5, hi5v⟩ := usize_add_ok i3 (alloc.vec.Vec.len n2) (by
      simp [hi3v, der_version_val]; omega)
    have hi5n : i5.val = (pkcs8Body (nums alg.val) (nums key.val)).length := by
      simp [hi5v, hi3v, der_version_val, hl2, hbl]
    unfold wrapBody at h
    simp [h0, h1, h2, hb0, hi3, hi5, core.result.Result.Insts.CoreOpsTry.branch,
      alloc.vec.Vec.new] at h
    obtain ⟨⟨r1, buf1⟩, hadd, h⟩ := bind_eq_ok_inv _ _ _ h
    obtain ⟨e, rfl⟩ := add_der_len_big b0 i5 (by omega) r1 buf1 hadd
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from] at h
  · unfold wrapBody at h
    simp [h0, core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨⟨r1, buf1⟩, hadd, h⟩ := bind_eq_ok_inv _ _ _ h
    obtain ⟨e, rfl⟩ := add_der_len_big n0 (Slice.len key) (by simpa using hk) r1 buf1 hadd
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from] at h

end Keystore2Verify.SwKeyblob
