import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: if the slice has fewer than 4 bytes, `consume_blob` returns an error whose root
cause is `INVALID_KEY_BLOB`, and the slice and the offset are returned unchanged. Hypotheses:
`BlobErrFmtLaws` and the law `CoreMemSizeOfSpec`. -/
theorem consume_blob_err_len (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : CoreMemSizeOfSpec) (data : Slice Std.U8) (next : Std.Usize)
    (blob : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_blob data next blob = ok (.Err e, data, next) ∧
      IsBlobErr root e := by
  sorry

/-- conditional: if the slice has at least 4 but fewer than 8 bytes (a length and no offset),
`consume_blob` returns an error whose root cause is `INVALID_KEY_BLOB`, the slice has moved
forward by 4 bytes, and the offset is unchanged. Hypotheses: `BlobErrFmtLaws` and the laws
`CoreMemSizeOfSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_err_offset (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h4 : 4 ≤ data.val.length)
    (h8 : data.val.length < 8) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 4 := by
  sorry

/-- conditional: if the offset read from the slice (`u32At data 4`) is not the expected offset
`next`, `consume_blob` returns an error whose root cause is `INVALID_KEY_BLOB`, the slice has
moved forward by 8 bytes, and the offset is unchanged. Hypotheses: the slice has at least 8 bytes,
the offsets differ, `BlobErrFmtLaws`, and the laws `CoreMemSizeOfSpec` and
`CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_err_mismatch (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 ≠ next.val) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 8 := by
  sorry

/-- conditional: if the offset is the expected one and the range `offset .. offset + length` goes
past the end of the blob data, `consume_blob` returns an error whose root cause is
`INVALID_KEY_BLOB`, the slice has moved forward by 8 bytes, and the offset is unchanged.
Hypotheses: the slice has at least 8 bytes, the offset read is `next`, the sum of offset and
length (`u32At data 0`) fits in a `usize` and is larger than the blob data, `BlobErrFmtLaws`, and
the laws `CoreMemSizeOfSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_err_past_end (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 = next.val)
    (hfit : next.val + u32At data.val 0 ≤ Std.Usize.max)
    (hend : blob.val.length < next.val + u32At data.val 0) :
    ∃ e data', sw_keyblob.consume_blob data next blob = ok (.Err e, data', next) ∧
      IsBlobErr root e ∧ data'.val = data.val.drop 8 := by
  sorry

/-- conditional: if the offset is the expected one and the sum of offset and length does not fit
in a `usize` (only possible when `usize` has 32 bits), `consume_blob` panics. Hypotheses: the
slice has at least 8 bytes, the offset read is `next`, the sum is larger than the largest
`usize`, and the laws `CoreMemSizeOfSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_fail_overflow (hsize : CoreMemSizeOfSpec)
    (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8) (next : Std.Usize)
    (blob : Slice Std.U8) (h : 8 ≤ data.val.length) (hoff : u32At data.val 4 = next.val)
    (hover : Std.Usize.max < next.val + u32At data.val 0) :
    ∃ x, sw_keyblob.consume_blob data next blob = fail x := by
  sorry

/-- conditional: if the offset is the expected one and the range fits in the blob data,
`consume_blob` returns `Ok` of the `n` bytes of the blob data from the offset (`n = u32At data
0`), the slice moves forward by 8 bytes, and the offset grows by `n`. Length 0 gives an empty
vector. Hypotheses: the slice has at least 8 bytes, the offset read is `next`, the range ends
inside the blob data, and the laws `CoreMemSizeOfSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_blob_ok (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (next : Std.Usize) (blob : Slice Std.U8) (h : 8 ≤ data.val.length)
    (hoff : u32At data.val 4 = next.val)
    (hend : next.val + u32At data.val 0 ≤ blob.val.length) :
    ∃ v data' next', sw_keyblob.consume_blob data next blob = ok (.Ok v, data', next') ∧
      v.val = (blob.val.drop next.val).take (u32At data.val 0) ∧
      data'.val = data.val.drop 8 ∧ next'.val = next.val + u32At data.val 0 := by
  sorry
end Keystore2Verify.SwKeyblob
