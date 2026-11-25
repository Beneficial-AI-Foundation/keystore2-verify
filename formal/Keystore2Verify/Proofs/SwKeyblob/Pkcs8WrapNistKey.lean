import Keystore2Verify.Proofs.Lemmas.SwKeyblobWrap

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
  rw [wrap_eq_body nist_key curve alg hc]
  exact wrap_body_ok alg nist_key hbody

/-- conditional: for a curve that is not one of the four NIST curves (Curve25519 included),
`pkcs8_wrap_nist_key` returns an error whose root cause is `INVALID_KEY_BLOB`. The curve is
checked first, so this holds for every key. Hypotheses: `BlobErrFmtLaws`. -/
theorem pkcs8_wrap_nist_key_err_curve (root : anyhow.Error → ErrRoot) (hlaw : BlobErrFmtLaws root)
    (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve) (hc : ¬ NistCurve curve) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e := by
  exact wrap_err_curve root hlaw nist_key curve hc

/-- conditional: for a NIST curve and a key longer than `0xffff` bytes, `pkcs8_wrap_nist_key`
returns an error whose root cause is `INVALID_KEY_BLOB` (the length of the octet string does not
fit in a DER length). Hypotheses: `BlobErrFmtLaws`. -/
theorem pkcs8_wrap_nist_key_err_key_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (hc : NistCurve curve) (hkey : 0xffff < nist_key.val.length) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e := by
  obtain ⟨alg, hc'⟩ := hc
  rw [wrap_eq_body nist_key curve alg hc']
  exact wrap_body_err_key root hlaw alg nist_key hkey

/-- conditional: for a NIST curve and a key of at most `0xffff` bytes whose wrapped content is
longer than `0xffff` bytes, `pkcs8_wrap_nist_key` returns an error whose root cause is
`INVALID_KEY_BLOB` (the length of the content does not fit in a DER length). Hypotheses: `alg` is
the identifier of `curve`, the key is at most `0xffff` bytes, the content is longer than `0xffff`
bytes, and `BlobErrFmtLaws`. -/
theorem pkcs8_wrap_nist_key_err_body_len (root : anyhow.Error → ErrRoot)
    (hlaw : BlobErrFmtLaws root) (nist_key : Slice Std.U8) (curve : EcCurve.EcCurve)
    (alg : Slice Std.U8) (hc : NistAlgId curve alg) (hkey : nist_key.val.length ≤ 0xffff)
    (hbody : 0xffff < (pkcs8Body (nums alg.val) (nums nist_key.val)).length) :
    ∃ e, sw_keyblob.pkcs8_wrap_nist_key nist_key curve = ok (.Err e) ∧ IsBlobErr root e := by
  rw [wrap_eq_body nist_key curve alg hc]
  exact wrap_body_err_body root hlaw alg nist_key (nist_alg_len curve alg hc) hkey hbody
end Keystore2Verify.SwKeyblob
