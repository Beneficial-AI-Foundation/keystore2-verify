import Keystore2Verify.Proofs.Lemmas.SwKeyblobReaders

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on a slice of fewer than 4 bytes, `consume_i32` returns an error whose root cause
is `INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrFmtLaws` and the
law `SizeOfLaw Std.I32 4`. -/
theorem consume_i32_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.I32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_i32 data = ok (.Err e, data) ∧ IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨n, hn, hn4⟩ := hsize
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.consume_i32
  rw [show sw_keyblob.consume_i32.LEN = ok n from by
    unfold sw_keyblob.consume_i32.LEN; exact hn]
  have hlt : data.val.length < n.val := by omega
  simp [hlt, he0, hs, core.hint.must_use, he1]

/-- conditional: on a slice of at least 4 bytes, `consume_i32` returns the `i32` whose bit
pattern is the little-endian number of the first 4 bytes, and the slice moves forward by 4
bytes. Hypotheses: the laws `SizeOfLaw Std.I32 4` and `CoreNumI32FromNeBytesSpec`. -/
theorem consume_i32_ok (hsize : SizeOfLaw Std.I32 4) (hfrom : CoreNumI32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_i32 data = ok (.Ok x, data') ∧
      x.bv = BitVec.ofNat 32 (u32At data.val 0) ∧ data'.val = data.val.drop 4 := by
  obtain ⟨n, hn, hn4⟩ := hsize
  unfold sw_keyblob.consume_i32
  rw [show sw_keyblob.consume_i32.LEN = ok n from by
    unfold sw_keyblob.consume_i32.LEN; exact hn]
  have hlt : ¬ data.val.length < 4 := by omega
  simp [hlt, h, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, hn4,
    core.array.TryFromArrayCopySlice.try_from]
  have hl : (data.val.take 4).length = 4 := by simp; omega
  simp [core.result.Result.unwrap]
  obtain ⟨x, hx, hbv⟩ := hfrom (Array.from (List.take 4 data.val) (by simpa using hl))
  refine ⟨x, data.drop 4#usize, by simp [hx], ?_, by simp⟩
  have h1 := congrArg BitVec.toNat hbv
  have h2 := h1.trans (BitVec.toNat_ofNat _ _)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simpa [u32At] using h2
end Keystore2Verify.SwKeyblob
