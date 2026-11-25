import Keystore2Verify.Specs.Defs.SwKeyblob

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
  sorry

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
  sorry

/-- conditional: if the blob has at least 21 bytes and `compute_hmac` on all bytes but the last 8
fails, then `new_from_serialized` returns the same `fail x`. Hypotheses: the outcome of
`compute_hmac`, and the law `SizeOfLaw Std.U32 4`. -/
theorem new_from_serialized_fail_hmac (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (h : minBlobLen ≤ data.val.length) (s : Slice Std.U8)
    (hs : s.val = data.val.take (data.val.length - 8)) (x : Error)
    (hmac : sw_keyblob.KeyBlob.compute_hmac s hidden = fail x) :
    sw_keyblob.KeyBlob.new_from_serialized data hidden = fail x := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Keystore2Verify.SwKeyblob
