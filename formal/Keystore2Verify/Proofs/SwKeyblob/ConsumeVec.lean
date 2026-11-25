import Keystore2Verify.Proofs.Lemmas.SwKeyblobReaders

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on a slice of fewer than 4 bytes (no length prefix), `consume_vec` returns an
error whose root cause is `INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses:
`BlobErrFmtLaws` and the law `SizeOfLaw Std.U32 4`. -/
theorem consume_vec_err_prefix (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_vec data = ok (.Err e, data) ∧ IsBlobErr root e := by
  obtain ⟨e, he, hr⟩ := consume_u32_err_aux root hlaw hsize data h
  refine ⟨e, ?_, hr⟩
  unfold sw_keyblob.consume_vec
  simp [he, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- conditional: if the length prefix is larger than the bytes after it, `consume_vec` returns an
error whose root cause is `INVALID_KEY_BLOB`, and the slice has moved forward by the 4 bytes of
the prefix. Hypotheses: the slice has at least 4 bytes, the prefix (`u32At data 0`) is larger than
the rest, `BlobErrFmtLaws`, and the laws `SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_vec_err_len (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (h : 4 ≤ data.val.length) (hlen : data.val.length - 4 < u32At data.val 0) :
    ∃ e data', sw_keyblob.consume_vec data = ok (.Err e, data') ∧ IsBlobErr root e ∧
      data'.val = data.val.drop 4 := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data h
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, data1, ?_, by unfold IsBlobErr; rw [hr1, hr0], hd1⟩
  have hlt : data1.val.length < x.val := by
    rw [hxv, hd1]; simp; omega
  unfold sw_keyblob.consume_vec
  simp [hx, core.result.Result.Insts.CoreOpsTry.branch, lift, hlt, he0, hs,
    core.hint.must_use, he1]

/-- conditional: if the length prefix `n` fits in the bytes after it, `consume_vec` returns `Ok`
of the `n` bytes after the prefix, and the slice moves forward by `4 + n` bytes. Length 0 gives
an empty vector. Hypotheses: the slice has at least 4 bytes, the prefix `n = u32At data 0` is at
most the rest, and the laws `SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_vec_ok (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length)
    (hlen : u32At data.val 0 ≤ data.val.length - 4) :
    ∃ v data', sw_keyblob.consume_vec data = ok (.Ok v, data') ∧
      v.val = (data.val.drop 4).take (u32At data.val 0) ∧
      data'.val = data.val.drop (4 + u32At data.val 0) := by
  obtain ⟨x, data1, hx, hxv, hd1⟩ := consume_u32_ok_aux hsize hfrom data h
  have hle : ¬ data1.val.length < x.val := by rw [hxv, hd1]; simp; omega
  have hle2 : x.val ≤ data1.val.length := by omega
  have hc : (UScalar.cast .Usize x).val = x.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by
      have := System.Platform.numBits_eq
      simp only [UScalarTy.numBits]; omega)
  obtain ⟨v, hv, hvv⟩ := to_vec_u8
    (Slice.from (List.take x.val data1.val) (by have := data1.property; simp))
  unfold sw_keyblob.consume_vec
  simp [hx, core.result.Result.Insts.CoreOpsTry.branch, lift, hle,
    hle2, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, hv]
  refine ⟨by simp [hvv, hxv, hd1], ?_⟩
  simp [hxv, hd1, List.drop_drop]
end Keystore2Verify.SwKeyblob
