import Keystore2Verify.Proofs.Lemmas.SwKeyblobReaders

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on a slice of fewer than 4 bytes, `consume_u32` returns an error whose root cause
is `INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrFmtLaws` and the
law `SizeOfLaw Std.U32 4` for `size_of`. -/
theorem consume_u32_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (hsize : SizeOfLaw Std.U32 4) (data : Slice Std.U8) (h : data.val.length < 4) :
    ∃ e, sw_keyblob.consume_u32 data = ok (.Err e, data) ∧ IsBlobErr root e := by
  exact consume_u32_err_aux root hlaw hsize data h

/-- conditional: on a slice of at least 4 bytes, `consume_u32` returns the number that the first
4 bytes spell in host byte order (little-endian: `u32At`), and the slice moves forward by 4
bytes. Hypotheses: the laws `SizeOfLaw Std.U32 4` and `CoreNumU32FromNeBytesSpec`. -/
theorem consume_u32_ok (hsize : SizeOfLaw Std.U32 4) (hfrom : CoreNumU32FromNeBytesSpec)
    (data : Slice Std.U8) (h : 4 ≤ data.val.length) :
    ∃ x data', sw_keyblob.consume_u32 data = ok (.Ok x, data') ∧
      x.val = u32At data.val 0 ∧ data'.val = data.val.drop 4 := by
  exact consume_u32_ok_aux hsize hfrom data h
end Keystore2Verify.SwKeyblob
