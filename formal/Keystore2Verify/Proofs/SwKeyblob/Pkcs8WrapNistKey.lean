import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: for a NIST curve and a key whose wrapped content is at most `0xffff` bytes long,
`pkcs8_wrap_nist_key` returns `Ok` of the PKCS#8 `PrivateKeyInfo` of the key (`pkcs8Wrap`), built
with the algorithm identifier of the curve. Hypotheses: `alg` is the identifier of `curve`, and
the length of `pkcs8Body alg key` is at most `0xffff`. -/
theorem pkcs8_wrap_nist_key_ok (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (alg : Slice Std.U8) (hc : NistAlgId curve alg)
    (hbody : (pkcs8Body (nums alg.val) (nums nist_key.val)).length ≤ 0xffff) :
    ∃ out, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Ok out) ∧
      nums out.val = pkcs8Wrap (nums alg.val) (nums nist_key.val) := by
  sorry

/-- conditional: for a curve that is not one of the four NIST curves (Curve25519 included),
`pkcs8_wrap_nist_key` returns an error whose root cause is `INVALID_KEY_BLOB`. The curve is
checked first, so this holds for every key. Hypotheses: `BlobErrLaws`. -/
theorem pkcs8_wrap_nist_key_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrLaws root)
    (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve) (hc : ¬ NistCurve curve) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: for a NIST curve and a key longer than `0xffff` bytes, `pkcs8_wrap_nist_key`
returns an error whose root cause is `INVALID_KEY_BLOB` (the length of the octet string does not
fit in a DER length). Hypotheses: `BlobErrLaws`. -/
theorem pkcs8_wrap_nist_key_err_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrLaws root) (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (hc : NistCurve curve) (hkey : 0xffff < nist_key.val.length) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e := by
  sorry

/-- conditional: for a NIST curve and a key of at most `0xffff` bytes whose wrapped content is
longer than `0xffff` bytes, `pkcs8_wrap_nist_key` returns an error whose root cause is
`INVALID_KEY_BLOB` (the length of the content does not fit in a DER length). Hypotheses:
`alg` is the identifier of `curve`, the key is at most `0xffff` bytes, the content is longer
than `0xffff` bytes, and `BlobErrLaws`. -/
theorem pkcs8_wrap_nist_key_err_body_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrLaws root) (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (alg : Slice Std.U8) (hc : NistAlgId curve alg) (hkey : nist_key.val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums nist_key.val)).length) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e := by
  sorry
end Keystore2Verify.SwKeyblob
