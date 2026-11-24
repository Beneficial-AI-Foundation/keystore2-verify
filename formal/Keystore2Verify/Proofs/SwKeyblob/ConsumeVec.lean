import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on a slice of fewer than 4 bytes (no length prefix), `consume_vec` returns an
error whose root cause is `INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses:
`BlobErrLaws` and the law `CoreMemSizeOfSpec`. -/
theorem consume_vec_err_prefix (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : CoreMemSizeOfSpec) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_vec data = ok (.Err e, data) ∧ IsBlobErr root e := by
  sorry

/-- conditional: if the length prefix is larger than the bytes after it, `consume_vec` returns
an error whose root cause is `INVALID_KEY_BLOB`, and the slice has moved forward by the 4 bytes
of the prefix. Hypotheses: the slice has at least 4 bytes, the prefix (`u32At data 0`) is larger
than the rest, `BlobErrLaws`, and the laws `CoreMemSizeOfSpec` and
`CoreNumU32FromNeBytesSpec`. -/
theorem consume_vec_err_len (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumU32FromNeBytesSpec) (data : Slice Std.U8)
    (h : 4 ≤ data.val.length) (hlen : data.val.length - 4 < u32At data.val 0) :
    ∃ e data', sw_keyblob.consume_vec data = ok (.Err e, data') ∧ IsBlobErr root e ∧
      data'.val = data.val.drop 4 := by
  sorry

/-- conditional: if the length prefix `n` fits in the bytes after it, `consume_vec` returns `Ok`
of the `n` bytes after the prefix, and the slice moves forward by `4 + n` bytes. Length 0 gives
an empty vector. Hypotheses: the slice has at least 4 bytes, the prefix `n = u32At data 0` is at
most the rest, and the laws `CoreMemSizeOfSpec` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_vec_ok (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length)
    (hlen : u32At data.val 0 ≤ data.val.length - 4) :
    ∃ v data', sw_keyblob.consume_vec data = ok (.Ok v, data') ∧
      v.val = (data.val.drop 4).take (u32At data.val 0) ∧
      data'.val = data.val.drop (4 + u32At data.val 0) := by
  sorry
end Keystore2Verify.SwKeyblob
