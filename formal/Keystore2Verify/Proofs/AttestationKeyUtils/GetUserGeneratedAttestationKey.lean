import Keystore2Verify.Specs.Defs.AttestationKeyUtils

namespace Keystore2Verify.AttestationKeyUtils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open attestation_key_utils renaming load_attest_key_blob_and_cert → loadAttest

/-- conditional: if `load_attest_key_blob_and_cert` returns an error `e`, then
`get_user_generated_attestation_key` returns an error with the same root cause, and the database
that the load returned. In the Rust source this path returns before the certificate is parsed.
Hypotheses: the outcome of the load; `format` and `from_str_nonconst` do not fail; the
assumption about `context` for an `anyhow::Error` (`AnyCtxLaw`). -/
theorem get_user_generated_attestation_key_load_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 ×
      database.BlobMetaData))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (e : anyhow.Error) (hload : loadAttest key caller_uid db = ok (.Err e, db1)) :
    ∃ e', attestation_key_utils.get_user_generated_attestation_key key caller_uid db =
        ok (.Err e', db1) ∧ root e' = root e := by
  sorry

/-- conditional: if the load returns the guard `g`, the key blob `blob`, the certificate `cert`
and the blob metadata `bmeta`, and parsing the certificate returns the crypto error `ce`, then
`get_user_generated_attestation_key` returns an error whose root cause is `ce`, and the database
that the load returned.
Hypotheses: the outcomes of the load and of `parse_subject_from_certificate` on the bytes of
`cert`; `format` and `from_str_nonconst` do not fail; the assumptions about `context` for an
`anyhow::Error` (`AnyCtxLaw`) and for a crypto error (`CryptoCtxLaw`). -/
theorem get_user_generated_attestation_key_parse_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 ×
      database.BlobMetaData))
    (hcrypto : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (g : database.KeyIdGuard) (blob cert : alloc.vec.Vec Std.U8) (bmeta : database.BlobMetaData)
    (hload : loadAttest key caller_uid db = ok (.Ok (g, blob, cert, bmeta), db1))
    (ce : keystore2_crypto.error.Error)
    (hparse : keystore2_crypto.parse_subject_from_certificate (alloc.vec.Vec.deref cert) =
      ok (.Err ce)) :
    ∃ e, attestation_key_utils.get_user_generated_attestation_key key caller_uid db =
        ok (.Err e, db1) ∧ root e = ErrRoot.crypto ce := by
  sorry

/-- conditional: if the load returns the guard `g`, the key blob `blob`, the certificate `cert`
and the blob metadata `bmeta`, and parsing the certificate returns the subject `subject`, then
`get_user_generated_attestation_key` returns `Ok (UserGenerated g blob bmeta subject)`, and the
database that the load returned. The blob and the certificate are moved, not changed.
Hypotheses: the outcomes of the load and of `parse_subject_from_certificate` on the bytes of
`cert`; `format` and `from_str_nonconst` do not fail; the assumptions about `context` for an
`anyhow::Error` (`AnyCtxLaw`) and for a crypto error (`CryptoCtxLaw`). -/
theorem get_user_generated_attestation_key_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 ×
      database.BlobMetaData))
    (hcrypto : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (g : database.KeyIdGuard) (blob cert : alloc.vec.Vec Std.U8) (bmeta : database.BlobMetaData)
    (hload : loadAttest key caller_uid db = ok (.Ok (g, blob, cert, bmeta), db1))
    (subject : alloc.vec.Vec Std.U8)
    (hparse : keystore2_crypto.parse_subject_from_certificate (alloc.vec.Vec.deref cert) =
      ok (.Ok subject)) :
    attestation_key_utils.get_user_generated_attestation_key key caller_uid db =
      ok (.Ok (attestation_key_utils.AttestationKeyInfo.UserGenerated g blob bmeta subject),
        db1) := by
  sorry
