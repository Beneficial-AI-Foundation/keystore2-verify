import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on an empty slice, `consume_u8` returns an error whose root cause is
`INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrLaws` and the law
`CoreSliceFirstSpec` for `first`. -/
theorem consume_u8_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (h : data.val = []) :
    ∃ e, sw_keyblob.consume_u8 data = ok (.Err e, data) ∧ IsBlobErr root e := by
  sorry

/-- conditional: on a slice that starts with the byte `b`, `consume_u8` returns `Ok b`, and the
slice moves forward by one byte. Hypothesis: the law `CoreSliceFirstSpec` for `first`. -/
theorem consume_u8_ok (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (b : Std.U8)
    (rest : List Std.U8) (h : data.val = b :: rest) :
    ∃ data', sw_keyblob.consume_u8 data = ok (.Ok b, data') ∧ data'.val = rest := by
  sorry
end Keystore2Verify.SwKeyblob
