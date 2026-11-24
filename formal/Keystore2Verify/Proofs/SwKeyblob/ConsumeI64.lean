import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on a slice of fewer than 8 bytes, `consume_i64` returns an error whose root
cause is `INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrLaws` and
the law `CoreMemSizeOfSpec`. -/
theorem consume_i64_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hsize : CoreMemSizeOfSpec) (data : Slice Std.U8) (h : data.val.length < 8) :
    ∃ e, sw_keyblob.consume_i64 data = ok (.Err e, data) ∧ IsBlobErr root e := by
  sorry

/-- conditional: on a slice of at least 8 bytes, `consume_i64` returns the `i64` whose bit
pattern is the little-endian number of the first 8 bytes, and the slice moves forward by 8
bytes. Hypotheses: the laws `CoreMemSizeOfSpec` and `CoreNumI64FromNeBytesSpec`. -/
theorem consume_i64_ok (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumI64FromNeBytesSpec)
    (data : Slice Std.U8) (h : 8 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_i64 data = ok (.Ok x, data') ∧
      x.bv = BitVec.ofNat 64 (leNat (data.val.take 8)) ∧ data'.val = data.val.drop 8 := by
  sorry
end Keystore2Verify.SwKeyblob
