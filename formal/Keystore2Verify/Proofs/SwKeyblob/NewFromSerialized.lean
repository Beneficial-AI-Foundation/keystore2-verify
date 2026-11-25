import Keystore2Verify.Proofs.Lemmas.SwKeyblobParseNew
import Keystore2Verify.Proofs.SwKeyblob.ComputeHmac

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: a blob of fewer than 21 bytes (empty included) gives an error whose root cause is
`INVALID_KEY_BLOB`. The length is checked first, so this holds for every `hidden`. Hypotheses:
`BlobErrFmtLaws` and the law `SizeOfLaw Std.U32 4`. -/
theorem new_from_serialized_err_short (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (h : data.val.length < minBlobLen) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨n, hn, hn4⟩ := hsize
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s, hs⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : data.val.length < 21 := by unfold minBlobLen at h; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, hn', mac_len_eq, h12, h13, h21, hlt, he0, hs, core.hint.must_use, he1]

/-- conditional: if the blob has at least 21 bytes and `compute_hmac` on all bytes but the last 8
returns `Err e`, then `new_from_serialized` returns the same error `e`: the error value is
passed through unchanged. Hypotheses: the outcome of `compute_hmac` (`s` is the bytes of the
blob but the last 8), and the law `SizeOfLaw Std.U32 4`. -/
theorem new_from_serialized_err_hmac
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (e : anyhow.Error)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Err e)) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) := by
  obtain ⟨n, hn, hn4⟩ := hsize
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have h8 : 8 ≤ data.val.length := by unfold minBlobLen at h; omega
  obtain ⟨z, hz, hzv⟩ := len_sub8 data h8
  have hzle : z.val ≤ data.val.length := by omega
  have key : ∀ pf, Slice.from (List.take z.val data.val) pf = s :=
    fun pf => Slice.ext _ _ (by simp [hs, hzv])
  have hlt : ¬ (data.val.length < 21) := by unfold minBlobLen at h; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, hn', mac_len_eq, hlt, h12, h13, h21, hz, hzle, key, hmac,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if the blob has at least 21 bytes and `compute_hmac` on all bytes but the last 8
fails, then `new_from_serialized` returns the same `fail x`. Hypotheses: the outcome of
`compute_hmac`, and the law `SizeOfLaw Std.U32 4`. -/
theorem new_from_serialized_fail_hmac (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (x : Error)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x := by
  obtain ⟨n, hn, hn4⟩ := hsize
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have h8 : 8 ≤ data.val.length := by unfold minBlobLen at h; omega
  obtain ⟨z, hz, hzv⟩ := len_sub8 data h8
  have hzle : z.val ≤ data.val.length := by omega
  have key : ∀ pf, Slice.from (List.take z.val data.val) pf = s :=
    fun pf => Slice.ext _ _ (by simp [hs, hzv])
  have hlt : ¬ (data.val.length < 21) := by unfold minBlobLen at h; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, hn', mac_len_eq, hlt, h12, h13, h21, hz, hzle, key, hmac,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if the last 8 bytes differ from the MAC that `compute_hmac` returns for the rest,
`new_from_serialized` returns an error whose root cause is `INVALID_KEY_BLOB`. This check comes
before the version check and before any parsing. Hypotheses: the blob has at least 21 bytes, the
outcome of `compute_hmac`, the last 8 bytes differ from it, `BlobErrLaws`, and the laws
`SizeOfLaw Std.U32 4` and `Shared0SliceNeSpec`. -/
theorem new_from_serialized_err_mac (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (m : alloc.vec.Vec Std.U8)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = ok (.Ok m))
    (hbad : data.val.drop (data.val.length - 8) ≠ m.val) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨⟨hnew, hctx, hfmt⟩, hstr⟩ := hlaw
  obtain ⟨z, b, hn, hz, hzv, key, hb, hbiff⟩ := nfs_mac_facts hsize hne data h s hs m
  have hbt : b = true := hbiff.2 hbad
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨a, ha⟩ := hstr (toStr "keystore2/src/sw_keyblob.rs:243: invalid key blob")
  obtain ⟨s2, hs2⟩ := hfmt a
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s2
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by unfold minBlobLen at h; omega
  have hzle : z.val ≤ data.val.length := by omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmac, hb, hbt, he0, ha, hs2,
    core.hint.must_use, he1, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if the MAC is good and the first byte is not 0, `new_from_serialized` returns an
error whose root cause is `INVALID_KEY_BLOB`. Hypotheses: `MacOk`, the first byte `v` is not 0,
`BlobErrFmtLaws`, and the laws `SizeOfLaw Std.U32 4`, `Shared0SliceNeSpec` and
`CoreSliceFirstSpec`. -/
theorem new_from_serialized_err_version (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hmac : MacOk data hidden) (v : Std.U8) (hv : data.val.head? = some v) (hv0 : v.val ≠ 0) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨hlen, s, m, hs, hmc, hdrop⟩ := hmac
  obtain ⟨z, b, hn, hz, hzv, key, hb, hbiff⟩ := nfs_mac_facts hsize hne data hlen s hs m
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd hdrop (hbiff.1 rfl)
  subst hbf
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by unfold minBlobLen at hlen; omega
  have hzle : z.val ≤ data.val.length := by omega
  obtain ⟨rest, hr⟩ : ∃ rest, data.val = v :: rest := by
    cases hd : data.val <;> simp_all
  obtain ⟨data1, hc8, -⟩ := consume_u8_ok hfirst data v rest hr
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s2, hs2⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s2
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hv0, he0, hs2, core.hint.must_use, he1, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if the MAC is good, the version is 0 and the key material length `u32At data 1`
is larger than the bytes after it, `new_from_serialized` returns an error whose root cause is
`INVALID_KEY_BLOB`. The 8 MAC bytes count as bytes after it. Hypotheses: `MacOk`, the version is
0, the length is too large, `BlobErrFmtLaws`, and the laws `SizeOfLaw Std.U32 4`,
`Shared0SliceNeSpec`, `CoreSliceFirstSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem new_from_serialized_err_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hmac : MacOk data hidden) (hv : data.val.head? = some 0#u8)
    (hlen : data.val.length - 5 < u32At data.val 1) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨hlen, s, m, hs, hmc, hdrop⟩ := hmac
  obtain ⟨z, b, hn, hz, hzv, key, hb, hbiff⟩ := nfs_mac_facts hsize hne data hlen s hs m
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd hdrop (hbiff.1 rfl)
  subst hbf
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by unfold minBlobLen at hlen; omega
  have hzle : z.val ≤ data.val.length := by omega
  obtain ⟨rest, hr⟩ : ∃ rest, data.val = 0#u8 :: rest := by
    cases hd : data.val <;> simp_all
  obtain ⟨data1, hc8, hd1⟩ := consume_u8_ok hfirst data 0#u8 rest hr
  have hd1' : data1.val = data.val.drop 1 := by rw [hd1, hr]; rfl
  have hu : u32At data1.val 0 = u32At data.val 1 := by simp [hd1', u32At]
  obtain ⟨e, data2, hcv, hbe, -⟩ := consume_vec_err_len root hlaw hsize hfrom data1
    (by rw [hd1']; simp; omega) (by rw [hu, hd1']; simp; omega)
  refine ⟨e, ?_, hbe⟩
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if all checks before the parameter lists pass and the first `deserialize_params`
returns `Err e`, then `new_from_serialized` returns the same error `e`: the error value is
passed through unchanged. Hypotheses: `PastKey`, `d2` is the blob after the key material
(`5 + u32At data 1` bytes dropped), the outcome of `deserialize_params d2`, and the laws
`SizeOfLaw Std.U32 4`, `Shared0SliceNeSpec`, `CoreSliceFirstSpec` and
`CoreNumU32FromNeBytesSpec`. -/
theorem new_from_serialized_err_hw
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (hfirst : CoreSliceFirstSpec)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1)) (e : anyhow.Error)
    (d3 : Slice Std.U8) (hdes : sw_keyblob.deserialize_params d2 = ok (.Err e, d3)) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if all checks before the parameter lists pass and the first `deserialize_params`
fails, then `new_from_serialized` returns the same `fail x`. Hypotheses: as for
`new_from_serialized_err_hw`, without `d3`, with the failure `x` as the
outcome of `deserialize_params d2`. -/
theorem new_from_serialized_fail_hw (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1)) (x : Error)
    (hdes : sw_keyblob.deserialize_params d2 = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if all checks before the parameter lists pass, the first `deserialize_params`
returns `Ok` and the second returns `Err e`, then `new_from_serialized` returns the same error
`e`: the error value is passed through unchanged. Hypotheses: as for
`new_from_serialized_err_hw`, with `d3` the slice that the first call leaves, and the outcomes
of both calls. -/
theorem new_from_serialized_err_sw
    (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec) (hfirst : CoreSliceFirstSpec)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3)) (e : anyhow.Error)
    (d4 : Slice Std.U8) (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Err e, d4)) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes1, hdes2, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if all checks before the parameter lists pass, the first `deserialize_params`
returns `Ok` and the second fails, then `new_from_serialized` returns the same `fail x`.
Hypotheses: as for `new_from_serialized_err_sw`, without `d4`, with the failure `x`
as the outcome of the second call. -/
theorem new_from_serialized_fail_sw (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3)) (x : Error)
    (hdes2 : sw_keyblob.deserialize_params d3 = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes1, hdes2, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if both parameter lists parse and the remaining slice is shorter than the MAC,
`new_from_serialized` ends in an outer failure. A reading of the Rust source shows that the slice
panic (`data[8..]`) is reachable. The Lean statement assumes the parser outcomes and the length
of the remainder. Hypotheses: all checks before the lists pass (`PastKey`), both calls of
`deserialize_params` return `Ok`, the slice `d4` that is left is shorter than 8 bytes, and the
laws `SizeOfLaw Std.U32 4`, `Shared0SliceNeSpec`, `CoreSliceFirstSpec` and
`CoreNumU32FromNeBytesSpec`. -/
theorem new_from_serialized_fail_rest (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length < 8) :
    ∃ x, sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  have hr8 : ¬ 8 ≤ d4.val.length := by omega
  refine ⟨Error.undef, ?_⟩
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes1, hdes2, hr8, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: both parameter lists parse and more than 8 bytes are left, so
`new_from_serialized` returns an error whose root cause is `INVALID_KEY_BLOB`. Hypotheses: as for
`new_from_serialized_fail_rest`, but `d4` is longer than 8 bytes, and `BlobErrFmtLaws`. -/
theorem new_from_serialized_err_extra (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : 8 < d4.val.length) :
    ∃ e, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Err e) ∧
      IsBlobErr root e := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  obtain ⟨hnew, hctx, hfmt⟩ := hlaw
  obtain ⟨e0, he0, hr0⟩ := hnew (error.Error.Km ErrorCode.ErrorCode.INVALID_KEY_BLOB)
  obtain ⟨s2, hs2⟩ := hfmt noArgs
  obtain ⟨e1, he1, hr1⟩ := hctx e0 s2
  refine ⟨e1, ?_, by unfold IsBlobErr; rw [hr1, hr0]⟩
  have hr8 : 8 ≤ d4.val.length := by omega
  have hgt : ¬ (d4.val.length ≤ 8) := by omega
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes1, hdes2, hr8, hgt, he0, hs2, core.hint.must_use, he1,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: both parameter lists parse and exactly 8 bytes are left, so
`new_from_serialized` returns `Ok` of a blob. Its key material is the `u32At data 1` bytes after
the length prefix, and its two parameter lists are the results of the two calls of
`deserialize_params`. Hypotheses: as for `new_from_serialized_fail_rest`, but `d4` has exactly 8
bytes. -/
theorem new_from_serialized_ok (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hpast : PastKey data hidden) (d2 : Slice Std.U8)
    (hd2 : d2.val = data.val.drop (5 + u32At data.val 1))
    (hw : alloc.vec.Vec KeyParam) (d3 : Slice Std.U8)
    (hdes1 : sw_keyblob.deserialize_params d2 = ok (.Ok hw, d3))
    (sw : alloc.vec.Vec KeyParam) (d4 : Slice Std.U8)
    (hdes2 : sw_keyblob.deserialize_params d3 = ok (.Ok sw, d4))
    (hrest : d4.val.length = 8) :
    ∃ kb, sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb) ∧
      kb.key_material.val = (data.val.drop 5).take (u32At data.val 1) ∧
      kb.hw_enforced = hw ∧ kb.sw_enforced = sw := by
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2'⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  have hdd : data2 = d2 := Slice.ext _ _ (by rw [hd2', hd2])
  subst hdd
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  have hr8 : 8 ≤ d4.val.length := by omega
  have hle8 : d4.val.length ≤ 8 := by omega
  refine ⟨⟨vec, hw, sw⟩, ?_, hvv, rfl, rfl⟩
  unfold sw_keyblob.KeyBlob.new_from_serialized
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, hdes1, hdes2, hr8, hle8, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]

/-- conditional: if `new_from_serialized` returns `Ok kb`, then the MAC check passed: the blob has
at least 21 bytes, and its last 8 bytes equal the MAC that `compute_hmac` returns for all bytes
but the last 8 and the hidden input that the function was given (`MacOk`). The outcome of
`compute_hmac` is derived from the observed success, not assumed. This is a fact about the control
flow of the function; it says nothing about the strength of the MAC. Hypotheses: the laws
`SizeOfLaw Std.U32 4` and `Shared0SliceNeSpec`. -/
theorem new_from_serialized_ok_mac (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (h : sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb)) :
    MacOk data hidden := by
  obtain ⟨n, hn, hn4⟩ := hsize
  have hn' : n = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hn4
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  by_cases hlt : data.val.length < 21
  · exfalso
    unfold sw_keyblob.KeyBlob.new_from_serialized at h
    simp [hn, hn', mac_len_eq, h12, h13, h21, hlt, bind_eq_ok_iff] at h
  · have h21' : minBlobLen ≤ data.val.length := by unfold minBlobLen; omega
    obtain ⟨z, hz, hzv⟩ := len_sub8 data (by omega)
    have hzle : z.val ≤ data.val.length := by omega
    obtain ⟨s, hs⟩ : ∃ s : Slice Std.U8, s.val = data.val.take (data.val.length - 8) :=
      ⟨Slice.from (data.val.take (data.val.length - 8))
        (by have := Slice.length_ineq data; simp; omega), by simp⟩
    have key : ∀ pf, Slice.from (List.take z.val data.val) pf = s :=
      fun pf => Slice.ext _ _ (by simp [hs, hzv])
    unfold sw_keyblob.KeyBlob.new_from_serialized at h
    simp [hn, hn', mac_len_eq, h12, h13, h21, hlt, hz, hzle, key,
      core.slice.index.SliceIndexRangeFromUsizeSlice.index,
      core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
    rcases result_trichotomy (sw_keyblob.KeyBlob.compute_hmac s hidden) with
      ⟨r, hr⟩ | ⟨x, hr⟩ | hr
    · cases r with
      | Ok m =>
        rw [hr] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨b, hb, hbiff⟩ := hne (data.drop z) m
        rw [hb] at h
        by_cases hbt : b = true
        · exfalso
          simp [hbt, bind_eq_ok_iff] at h
        · refine ⟨h21', s, m, hs, hr, ?_⟩
          by_contra hcon
          exact hbt (hbiff.2 (by simpa [Slice.drop, hzv] using hcon))
      | Err e =>
        rw [hr] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] at h
    · rw [hr] at h
      simp at h
    · rw [hr] at h
      simp at h

/-- A successful parse passes all the checks before the parameter lists. -/
private theorem nfs_pastkey_of_ok (hsize : SizeOfLaw Std.U32 4) (hne : Shared0SliceNeSpec)
    (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (h : sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb)) :
    PastKey data hidden := by
  have hmac := new_from_serialized_ok_mac hsize hne data hidden kb h
  obtain ⟨hlen, s, m, hs, hmc, hdrop⟩ := hmac
  obtain ⟨z, b, hn, hz, hzv, key, hb, hbiff⟩ := nfs_mac_facts hsize hne data hlen s hs m
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd hdrop (hbiff.1 rfl)
  subst hbf
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by unfold minBlobLen at hlen; omega
  have hzle : z.val ≤ data.val.length := by omega
  obtain ⟨v, rest, hr⟩ : ∃ v rest, data.val = v :: rest := by
    cases hd : data.val with
    | nil => rw [hd] at hlen; simp [minBlobLen] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  obtain ⟨data1, hc8, hd1⟩ := consume_u8_ok hfirst data v rest hr
  have hd1' : data1.val = data.val.drop 1 := by rw [hd1, hr]; rfl
  unfold sw_keyblob.KeyBlob.new_from_serialized at h
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  by_cases hv : v.val = 0
  · have hv0 : v = 0#u8 := UScalar.eq_of_val_eq (by simpa using hv)
    subst hv0
    simp [key_blob_version_eq] at h
    rcases result_trichotomy (sw_keyblob.consume_vec data1) with
      ⟨⟨r2, d2⟩, hcv⟩ | ⟨x, hcv⟩ | hcv
    · cases r2 with
      | Ok vec =>
        refine ⟨⟨hlen, s, m, hs, hmc, hdrop⟩, by rw [hr]; rfl, ?_⟩
        by_contra hle
        have hu : u32At data1.val 0 = u32At data.val 1 := by simp [hd1', u32At]
        have hbig : data1.val.length - 4 < u32At data1.val 0 := by
          rw [hu, hd1']; simp; omega
        obtain ⟨e, he⟩ := consume_vec_big hsize hfrom data1 (by rw [hd1']; simp; omega) hbig
          _ _ hcv
        cases he
      | Err e =>
        rw [hcv] at h
        simp at h
    · rw [hcv] at h
      simp at h
    · rw [hcv] at h
      simp at h
  · exfalso
    simp [hv, key_blob_version_eq, bind_eq_ok_iff] at h

/-- Successful parsing recovers the key field and the two decoder results in order. The
opaque decoders determine both the parameter values and the slices they leave. -/
theorem new_from_serialized_ok_layout_of_result (hsize : SizeOfLaw Std.U32 4)
    (hne : Shared0SliceNeSpec) (hfirst : CoreSliceFirstSpec) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (kb : sw_keyblob.KeyBlob)
    (h : sw_keyblob.KeyBlob.new_from_serialized data hidden = ok (.Ok kb)) :
    PastKey data hidden ∧ kb.key_material.val = (data.val.drop 5).take (u32At data.val 1) ∧
      ∃ d2 d3 d4, d2.val = data.val.drop (5 + u32At data.val 1) ∧
        sw_keyblob.deserialize_params d2 = ok (.Ok kb.hw_enforced, d3) ∧
        sw_keyblob.deserialize_params d3 = ok (.Ok kb.sw_enforced, d4) ∧ d4.val.length = 8 := by
  have hpast := nfs_pastkey_of_ok hsize hne hfirst hfrom data hidden kb h
  obtain ⟨z, s, m, data1, data2, vec, hn, hz, hzle, key, hmc, hb, hc8, hd1, hcv, hvv, hd2⟩ :=
    nfs_key_facts hsize hne hfirst hfrom data hidden hpast
  obtain ⟨h12, h13, h21⟩ := nfs_consts
  have hlt : ¬ (data.val.length < 21) := by
    have := hpast.1.1; unfold minBlobLen at this; omega
  unfold sw_keyblob.KeyBlob.new_from_serialized at h
  simp [hn, mac_len_eq, h12, h13, h21, hlt, hz, hzle, key, hmc, hb, hc8, key_blob_version_eq,
    hcv, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  refine ⟨hpast, ?_⟩
  rcases result_trichotomy (sw_keyblob.deserialize_params data2) with
    ⟨⟨r3, d3⟩, h3⟩ | ⟨x, h3⟩ | h3
  · cases r3 with
    | Ok hw =>
      rw [h3] at h
      simp at h
      rcases result_trichotomy (sw_keyblob.deserialize_params d3) with
        ⟨⟨r4, d4⟩, h4⟩ | ⟨x, h4⟩ | h4
      · cases r4 with
        | Ok sw =>
          rw [h4] at h
          simp at h
          by_cases h8 : 8 ≤ d4.val.length
          · by_cases hle : d4.val.length ≤ 8
            · simp [h8, hle] at h
              subst h
              exact ⟨hvv, data2, d3, d4, hd2, h3, h4, by omega⟩
            · exfalso
              simp [h8, hle, bind_eq_ok_iff] at h
          · simp [h8] at h
        | Err e =>
          rw [h4] at h
          simp at h
      · rw [h4] at h
        simp at h
      · rw [h4] at h
        simp at h
    | Err e =>
      rw [h3] at h
      simp at h
  · rw [h3] at h
    simp at h
  · rw [h3] at h
    simp at h

end Keystore2Verify.SwKeyblob
