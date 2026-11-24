import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: for a length up to `0xffff`, `add_der_len` appends the DER encoding of the
length (`derLen`) to the buffer and returns `Ok ()`. The bytes already in the buffer stay.
Hypotheses: the length is at most `0xffff`, and the encoding fits in the buffer (one push
per byte of `derLen len`). -/
theorem add_der_len_ok (buf : alloc.vec.Vec Std.U8) (len : Std.Usize)
    (hlen : len.val ≤ 0xffff) (hcap : buf.val.length + (derLen len.val).length ≤ Std.Usize.max) :
    ∃ buf', sw_keyblob.add_der_len buf len = ok (.Ok (), buf') ∧
      nums buf'.val = nums buf.val ++ derLen len.val := by
  sorry

/-- exact: for a length up to `0xffff`, if the buffer has no room for the encoding (one push per
byte of `derLen len`), `add_der_len` panics: one of its pushes fails. -/
theorem add_der_len_fail_capacity (buf : alloc.vec.Vec Std.U8) (len : Std.Usize)
    (hlen : len.val ≤ 0xffff)
    (hover : Std.Usize.max < buf.val.length + (derLen len.val).length) :
    ∃ x, sw_keyblob.add_der_len buf len = fail x := by
  sorry

/-- conditional: for a length above `0xffff`, `add_der_len` returns an error whose root cause is
`INVALID_KEY_BLOB`, and the buffer is returned unchanged. Hypotheses: the length is above
`0xffff`, and the shared laws of `BlobErrLaws`. -/
theorem add_der_len_err (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (buf : alloc.vec.Vec Std.U8) (len : Std.Usize) (hlen : 0xffff < len.val) :
    ∃ e, sw_keyblob.add_der_len buf len = ok (.Err e, buf) ∧ IsBlobErr root e := by
  sorry
end Keystore2Verify.SwKeyblob
