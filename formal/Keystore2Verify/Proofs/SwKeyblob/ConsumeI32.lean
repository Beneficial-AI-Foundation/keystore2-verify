import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on a slice of fewer than 4 bytes, `consume_i32` returns an error whose root cause
is `INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrFmtLaws` and the
law `CoreMemSizeOfSpec`. -/
theorem consume_i32_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : CoreMemSizeOfSpec) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_i32 data = ok (.Err e, data) ∧ IsBlobErr root e := by
  sorry

/-- conditional: on a slice of at least 4 bytes, `consume_i32` returns the `i32` whose bit
pattern is the little-endian number of the first 4 bytes, and the slice moves forward by 4
bytes. Hypotheses: the laws `CoreMemSizeOfSpec` and `CoreNumI32FromNeBytesSpec`. -/
theorem consume_i32_ok (hsize : CoreMemSizeOfSpec) (hfrom : CoreNumI32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_i32 data = ok (.Ok x, data') ∧
      x.bv = BitVec.ofNat 32 (u32At data.val 0) ∧ data'.val = data.val.drop 4 := by
  sorry
end Keystore2Verify.SwKeyblob
