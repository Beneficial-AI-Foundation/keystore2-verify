import Keystore2Verify.Proofs.Lemmas.SwKeyblobReaders

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: for a length up to `0xffff`, `add_der_len` appends the DER encoding of the
length (`derLen`) to the buffer and returns `Ok ()`. The bytes already in the buffer stay.
Hypotheses: the length is at most `0xffff`, and the encoding fits in the buffer (one push
per byte of `derLen len`). The capacity bound is the one of the Aeneas vector model (at most
`usize::MAX` bytes); Rust allows `isize::MAX` bytes and reaches its limit earlier, and between the
two bounds the model returns a value where Rust panics. So this statement describes the model and
is not a capacity guarantee for the Rust code. -/
theorem add_der_len_ok (buf : alloc.vec.Vec Std.U8) (len : Std.Usize)
    (hlen : len.val ≤ 0xffff)
    (hcap : buf.val.length + (derLen len.val).length ≤ Std.Usize.max) :
    ∃ buf', sw_keyblob.add_der_len buf len = ok (.Ok (), buf') ∧
      nums buf'.val = nums buf.val ++ derLen len.val := by
  have hu8 : ∀ n : Nat, n < 256 → n % 256 = n := fun n h => Nat.mod_eq_of_lt h
  unfold sw_keyblob.add_der_len
  by_cases h1 : len.val ≤ 127
  · obtain ⟨b1, hb1, hv1⟩ := push_ok_aux buf (UScalar.cast .U8 len)
      (by simp [derLen, h1] at hcap; omega)
    simp [lift, h1, hb1]
    simp [nums, hv1, derLen, h1, UScalar.cast_val_eq,
      Nat.mod_eq_of_lt (show len.val < 256 by omega)]
  by_cases h2 : len.val ≤ 255
  · have hd : derLen len.val = [0x81, len.val] := by simp [derLen, h1, h2]
    rw [hd] at hcap
    obtain ⟨b1, hb1, hv1⟩ := push_ok_aux buf 129#u8 (by simp at hcap; omega)
    obtain ⟨b2, hb2, hv2⟩ := push_ok_aux b1 (UScalar.cast .U8 len)
      (by rw [hv1]; simp at hcap ⊢; omega)
    simp [lift, h1, h2, hb1, hb2]
    simp [nums, hv2, hv1, hd, UScalar.cast_val_eq,
      Nat.mod_eq_of_lt (show len.val < 256 by omega)]
  · have hd : derLen len.val = [0x82, len.val / 256, len.val % 256] := by
      simp [derLen, h1, h2]
    rw [hd] at hcap
    obtain ⟨z, hz, hzv⟩ := usize_shr8 len
    obtain ⟨b1, hb1, hv1⟩ := push_ok_aux buf 130#u8 (by simp at hcap; omega)
    obtain ⟨b2, hb2, hv2⟩ := push_ok_aux b1 (UScalar.cast .U8 z)
      (by rw [hv1]; simp at hcap ⊢; omega)
    obtain ⟨b3, hb3, hv3⟩ := push_ok_aux b2 (UScalar.cast .U8 (len &&& 255#usize))
      (by rw [hv2, hv1]; simp at hcap ⊢; omega)
    have hl : len.val ≤ 65535 := hlen
    simp [lift, h1, h2, hl, hz, hb1, hb2, hb3]
    simp [nums, hv3, hv2, hv1, hd, UScalar.cast_val_eq, hzv,
      Nat.mod_eq_of_lt (show len.val / 256 < 256 by omega)]
    have : len.val &&& 255 = len.val % 256 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod len.val 8
    simp [this]

/-- exact: for a length up to `0xffff`, if the buffer has no room for the encoding (one push per
byte of `derLen len`), a push fails and `add_der_len` returns `fail .maximumSizeExceeded`. Room means the bound of the
Aeneas vector model (at most `usize::MAX` bytes). In Rust the panic comes at the lower limit of
`isize::MAX` bytes, so this statement describes the model and is not a capacity guarantee for the
Rust code. -/
theorem add_der_len_fail_capacity (buf : alloc.vec.Vec Std.U8) (len : Std.Usize)
    (hlen : len.val ≤ 0xffff)
    (hover : Std.Usize.max < buf.val.length + (derLen len.val).length) :
    sw_keyblob.add_der_len buf len = fail .maximumSizeExceeded := by
  unfold sw_keyblob.add_der_len
  by_cases h1 : len.val ≤ 127
  · have hd : derLen len.val = [len.val] := by simp [derLen, h1]
    rw [hd] at hover
    simp [lift, h1, push_fail_aux buf _ (by simpa using hover)]
  by_cases h2 : len.val ≤ 255
  · have hd : derLen len.val = [0x81, len.val] := by simp [derLen, h1, h2]
    rw [hd] at hover
    simp at hover
    by_cases c1 : buf.val.length + 1 ≤ Std.Usize.max
    · obtain ⟨b1, hb1, hv1⟩ := push_ok_aux buf 129#u8 c1
      simp [lift, h1, h2, hb1, push_fail_aux b1 _ (by rw [hv1]; simp; omega)]
    · simp [lift, h1, h2, push_fail_aux buf _ (by omega)]
  · have hd : derLen len.val = [0x82, len.val / 256, len.val % 256] := by
      simp [derLen, h1, h2]
    rw [hd] at hover
    simp at hover
    have hl : len.val ≤ 65535 := hlen
    obtain ⟨z, hz, hzv⟩ := usize_shr8 len
    by_cases c1 : buf.val.length + 1 ≤ Std.Usize.max
    · obtain ⟨b1, hb1, hv1⟩ := push_ok_aux buf 130#u8 c1
      by_cases c2 : b1.val.length + 1 ≤ Std.Usize.max
      · obtain ⟨b2, hb2, hv2⟩ := push_ok_aux b1 (UScalar.cast .U8 z) c2
        simp [lift, h1, h2, hl, hz, hb1, hb2,
          push_fail_aux b2 _ (by rw [hv2, hv1]; simp; omega)]
      · simp [lift, h1, h2, hl, hz, hb1, push_fail_aux b1 _ (by omega)]
    · simp [lift, h1, h2, hl, push_fail_aux buf _ (by omega)]

/-- conditional: for a length above `0xffff`, `add_der_len` returns an error whose root cause is
`INVALID_KEY_BLOB`, and the buffer is returned unchanged. Hypotheses: the length is above
`0xffff`, and the shared laws of `BlobErrFmtLaws`. -/
theorem add_der_len_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (buf : alloc.vec.Vec Std.U8) (len : Std.Usize) (hlen : 0xffff < len.val) :
    ∃ e, sw_keyblob.add_der_len buf len = ok (.Err e, buf) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  have h1 : ¬ len.val ≤ 127 := by omega
  have h2 : ¬ len.val ≤ 255 := by omega
  have h3 : ¬ len.val ≤ 65535 := by omega
  unfold sw_keyblob.add_der_len
  simp [h1, h2, h3, he0, hs, core.hint.must_use, he1]
end Keystore2Verify.SwKeyblob
