import Keystore2Verify.Proofs.Lemmas.SwKeyblobReaders

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: if the slice has fewer than 4 bytes, `consume_blob` returns an error whose root
cause is `INVALID_KEY_BLOB`, and the slice and the offset are returned unchanged. Hypotheses:
`BlobErrFmtLaws` and the law `SizeOfLaw Std.U32 4`. -/
theorem consume_blob_err_len (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (next : Std.Usize)
    (blob : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_blob data next blob = ok (.Err e, data, next) ∧
      IsBlobErr root e := by
  obtain ⟨e, he, hr⟩ := consume_u32_err_aux root hlaw hsize data h
  refine ⟨e, ?_, hr⟩
  unfold sw_keyblob.consume_blob
  simp [he, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- conditional: if the slice has at least 4 but fewer than 8 bytes (a length and no offset),
`consume_blob` returns an error whose root cause is `INVALID_KEY_BLOB`, the slice has moved
forward by 4 bytes, and the offset is unchanged. Hypotheses: `BlobErrFmtLaws` and the laws
`SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_err_offset (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h4 : 4 ≤ data.val.length)
    (h8 : data.val.length < 8) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 4 := by
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data (by omega)
  obtain ⟨e, he, hr⟩ := consume_u32_err_aux root hlaw hsize data1 (by rw [hd1]; simp; omega)
  refine ⟨e, data1, ?_, hr, hd1⟩
  unfold sw_keyblob.consume_blob
  simp [hx, he, core.result.Result.Insts.CoreOpsTry.branch, lift,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- conditional: if the offset read from the slice (`u32At data 4`) is not the expected offset
`next`, `consume_blob` returns an error whose root cause is `INVALID_KEY_BLOB`, the slice has
moved forward by 8 bytes, and the offset is unchanged. Hypotheses: the slice has at least 8 bytes,
the offsets differ, `BlobErrFmtLaws`, and the laws `SizeOfLaw Std.U32 4` and
`CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_err_mismatch (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 ≠ next.val) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 8 := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data (by omega)
  obtain ⟨y, data2, hy, hyv, hd2⟩ := consume_u32_ok_aux hsize hfrom data1
    (by rw [hd1]; simp; omega)
  have hyv' : y.val = u32At data.val 4 := by rw [hyv, hd1, u32At_drop_four]
  have hd2' : data2.val = data.val.drop 8 := by rw [hd2, hd1]; simp [List.drop_drop]
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, data2, ?_, by unfold IsBlobErr; rw [hr1, hr0], hd2'⟩
  have hne : y.val ≠ next.val := by rw [hyv']; exact hoff
  unfold sw_keyblob.consume_blob
  simp [hx, hy, core.result.Result.Insts.CoreOpsTry.branch, lift, he0, hs,
    core.hint.must_use, he1, hne]

/-- conditional: if the offset is the expected one and the range `offset .. offset + length` goes
past the end of the blob data, `consume_blob` returns an error whose root cause is
`INVALID_KEY_BLOB`, the slice has moved forward by 8 bytes, and the offset is unchanged.
Hypotheses: the slice has at least 8 bytes, the offset read is `next`, the sum of offset and
length (`u32At data 0`) fits in a `usize` and is larger than the blob data, `BlobErrFmtLaws`, and
the laws `SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_err_past_end (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 = next.val)
    (hfit : next.val + u32At data.val 0 ≤ Std.Usize.max)
    (hend : blob.val.length < next.val + u32At data.val 0) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 8 := by
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data (by omega)
  obtain ⟨y, data2, hy, hyv, hd2⟩ := consume_u32_ok_aux hsize hfrom data1
    (by rw [hd1]; simp; omega)
  have hyv' : y.val = u32At data.val 4 := by rw [hyv, hd1, u32At_drop_four]
  have hd2' : data2.val = data.val.drop 8 := by rw [hd2, hd1]; simp [List.drop_drop]
  have hyn : UScalar.cast .Usize y = next :=
    UScalar.eq_of_val_eq (by simp [hyv', hoff])
  have hyeq : y.val = next.val := by rw [hyv', hoff]
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨z, hz, hzv⟩ := usize_add_ok next (UScalar.cast .Usize x) (by simp [hxv]; omega)
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, data2, ?_, by unfold IsBlobErr; rw [hr1, hr0], hd2'⟩
  have hgt : blob.val.length < z.val := by rw [hzv]; simp [hxv]; omega
  unfold sw_keyblob.consume_blob
  simp [hx, hy, core.result.Result.Insts.CoreOpsTry.branch, lift, hyeq, hyn, hz, hgt, he0, hs,
    core.hint.must_use, he1]

/-- conditional: if the offset is the expected one and the sum of offset and length does not fit
in a `usize` (only possible when `usize` has 32 bits), `consume_blob` returns `fail .integerOverflow`. Hypotheses: the
slice has at least 8 bytes, the offset read is `next`, the sum is larger than the largest
`usize`, and the laws `SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_fail_overflow (hsize : SizeOfLaw Std.U32 4)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (next : Std.Usize)
    (blob : Slice Std.U8) (h : 8 ≤ data.val.length) (hoff : u32At data.val 4 = next.val)
    (hover : Std.Usize.max < next.val + u32At data.val 0) :
    sw_keyblob.consume_blob data next blob = fail .integerOverflow := by
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data (by omega)
  obtain ⟨y, data2, hy, hyv, hd2⟩ := consume_u32_ok_aux hsize hfrom data1
    (by rw [hd1]; simp; omega)
  have hyv' : y.val = u32At data.val 4 := by rw [hyv, hd1, u32At_drop_four]
  have hd2' : data2.val = data.val.drop 8 := by rw [hd2, hd1]; simp [List.drop_drop]
  have hyn : UScalar.cast .Usize y = next :=
    UScalar.eq_of_val_eq (by simp [hyv', hoff])
  have hyeq : y.val = next.val := by rw [hyv', hoff]
  have hov : Std.Usize.max < next.val + (UScalar.cast .Usize x).val := by simp [hxv]; omega
  unfold sw_keyblob.consume_blob
  simp [hx, hy, core.result.Result.Insts.CoreOpsTry.branch, lift, hyeq, hyn, usize_add_fail _ _ hov]

/-- conditional: if the offset is the expected one and the range fits in the blob data,
`consume_blob` returns `Ok` of the `n` bytes of the blob data from the offset (`n = u32At data
0`), the slice moves forward by 8 bytes, and the offset grows by `n`. Length 0 gives an empty
vector. Hypotheses: the slice has at least 8 bytes, the offset read is `next`, the range ends
inside the blob data, and the laws `SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_ok (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 = next.val)
    (hend : next.val + u32At data.val 0 ≤ blob.val.length) :
    ∃ v data' next', sw_keyblob.consume_blob data next blob = ok (.Ok v, data', next') ∧
      v.val = (blob.val.drop next.val).take (u32At data.val 0) ∧
      data'.val = data.val.drop 8 ∧ next'.val = next.val + u32At data.val 0 := by
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data (by omega)
  obtain ⟨y, data2, hy, hyv, hd2⟩ := consume_u32_ok_aux hsize hfrom data1
    (by rw [hd1]; simp; omega)
  have hyv' : y.val = u32At data.val 4 := by rw [hyv, hd1, u32At_drop_four]
  have hd2' : data2.val = data.val.drop 8 := by rw [hd2, hd1]; simp [List.drop_drop]
  have hyn : UScalar.cast .Usize y = next :=
    UScalar.eq_of_val_eq (by simp [hyv', hoff])
  have hyeq : y.val = next.val := by rw [hyv', hoff]
  obtain ⟨z, hz, hzv⟩ := usize_add_ok next (UScalar.cast .Usize x)
    (by simp [hxv]; have := Slice.length_ineq blob; omega)
  have hle : ¬ blob.val.length < z.val := by rw [hzv]; simp [hxv]; omega
  have hle1 : next.val ≤ z.val := by rw [hzv]; simp
  have hle2 : z.val ≤ blob.val.length := by omega
  obtain ⟨v, hv, hvv⟩ := to_vec_u8 (Slice.from (List.slice next.val z.val blob.val)
    (by have := Slice.length_ineq blob; simp [List.slice]; omega))
  unfold sw_keyblob.consume_blob
  simp [hx, hy, core.result.Result.Insts.CoreOpsTry.branch, lift, hyeq, hyn, hz, hle,
    core.slice.index.SliceIndexRangeUsizeSlice.index, hle1, hle2, hv]
  refine ⟨?_, ?_⟩
  · simp [hvv, List.slice, hzv, hxv]
  · simp [hzv, hxv, hd2']
end Keystore2Verify.SwKeyblob
