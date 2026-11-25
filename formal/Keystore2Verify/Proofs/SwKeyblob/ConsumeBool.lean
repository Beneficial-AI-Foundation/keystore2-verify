import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: on an empty slice, `consume_bool` returns an error whose root cause is
`INVALID_KEY_BLOB`, and the slice is returned unchanged. Hypotheses: `BlobErrLaws` and the law
`CoreSliceFirstSpec`. -/
theorem consume_bool_err_empty (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (h : data.val = []) :
    ∃ e, sw_keyblob.consume_bool data = ok (.Err e, data) ∧ IsBlobErr root e := by
  sorry

/-- conditional: on a slice that starts with the byte 1, `consume_bool` returns `Ok true`, and
the slice moves forward by one byte. Hypothesis: the law `CoreSliceFirstSpec`. -/
theorem consume_bool_true (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8)
    (rest : List Std.U8) (h : data.val = 1#u8 :: rest) :
    ∃ data', sw_keyblob.consume_bool data = ok (.Ok true, data') ∧ data'.val = rest := by
  sorry

/-- conditional: on a slice that starts with a byte other than 1 (0 included), `consume_bool`
returns an error whose root cause is `INVALID_KEY_BLOB`, and the slice has moved forward by one
byte. It never returns `Ok false`. Hypotheses: `BlobErrLaws` and the law `CoreSliceFirstSpec`. -/
theorem consume_bool_err_value (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (hfirst : CoreSliceFirstSpec) (data : Slice Std.U8) (b : Std.U8) (rest : List Std.U8)
    (h : data.val = b :: rest) (hb : b.val ≠ 1) :
    ∃ e data', sw_keyblob.consume_bool data = ok (.Err e, data') ∧ IsBlobErr root e ∧
      data'.val = rest := by
  sorry
end Keystore2Verify.SwKeyblob
