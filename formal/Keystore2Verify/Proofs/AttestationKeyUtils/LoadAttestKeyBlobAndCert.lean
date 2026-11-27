import Keystore2Verify.Specs.Defs.AttestationKeyUtils

namespace Keystore2Verify.AttestationKeyUtils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals Keystore2Verify.Permission
open android_system_keystore2.aidl.android.system.keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open attestation_key_utils.load_attest_key_blob_and_cert.closure.Insts
  renaming CoreOpsFunctionFnPairShared0KeyDescriptorOptionKeyPermSetResultTupleError → loadCheck
open database.KeystoreDB renaming load_key_entry → loadKeyEntry

/-- conditional: for the domain `BLOB` (3), `load_attest_key_blob_and_cert` returns an error whose
root cause is the keystore2 error `Km(INVALID_ARGUMENT)`, and the database `db` unchanged. In the
Rust source this path returns before `load_key_entry` is called.
Hypotheses: the external constant `ErrorCode::INVALID_ARGUMENT` is `ec`; `format` and
`from_str_nonconst` do not fail; the assumption about `context` for a keystore2 error
(`KsCtxAssumption`). -/
theorem load_attest_key_blob_and_cert_blob (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsCtxAssumption root Loaded) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.INVALID_ARGUMENT = ok ec)
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db : database.KeystoreDB)
    (hd : key.domain = 3#i32) :
    ∃ e, attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e, db) ∧ root e = ErrRoot.ks (error.Error.Km ec) := by
  sorry

/-- conditional: for a domain other than `BLOB`, if `load_key_entry` (with the key type `Client`,
the load bits `BOTH` and the permission check `Use`) returns an error `e`, the result is an error
with the same root cause, and the database that `load_key_entry` returned.
Hypotheses: the outcome of `load_key_entry` (a database read that may sleep and retry);
`format` and `from_str_nonconst` do not fail; the assumption about `context` for an `anyhow::Error`
(`AnyCtxLaw`). -/
theorem load_attest_key_blob_and_cert_load_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (hd : key.domain ≠ 3#i32) (e : anyhow.Error)
    (hload : loadKeyEntry loadCheck db key database.KeyType.Client
      database.KeyEntryLoadBits.BOTH caller_uid () = ok (.Err e, db1)) :
    ∃ e', attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e', db1) ∧ root e' = root e := by
  sorry

/-- conditional: for a domain other than `BLOB`, if `load_key_entry` returns an entry with no key
blob (`key_blob_info = none`), the result is an error whose root cause is the keystore2 error
`Rc(INVALID_ARGUMENT)`, and the database that `load_key_entry` returned.
Hypotheses: the outcome of `load_key_entry`; `format` and `from_str_nonconst` do not fail; the
assumptions of `context` for an `anyhow::Error` (`AnyCtxLaw`) and for a keystore2 error
(`KsCtxAssumption`). -/
theorem load_attest_key_blob_and_cert_no_blob (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8 × database.BlobMetaData))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (hd : key.domain ≠ 3#i32) (g : database.KeyIdGuard) (entry : database.KeyEntry)
    (hload : loadKeyEntry loadCheck db key database.KeyType.Client
      database.KeyEntryLoadBits.BOTH caller_uid () = ok (.Ok (g, entry), db1))
    (hblob : entry.key_blob_info = none) :
    ∃ e, attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e, db1) ∧ root e = ErrRoot.ks invalidArgumentError := by
  sorry

/-- conditional: for a domain other than `BLOB`, if `load_key_entry` returns an entry with a key
blob and no certificate (`cert = none`), the result is an error whose root cause is the keystore2
error `Rc(INVALID_ARGUMENT)`, and the database that `load_key_entry` returned.
Hypotheses: the outcome of `load_key_entry`; `format` and `from_str_nonconst` do not fail; the
assumptions of `context` for an `anyhow::Error` (`AnyCtxLaw`) and for a keystore2 error
(`KsCtxAssumption`). -/
theorem load_attest_key_blob_and_cert_no_cert (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8 × database.BlobMetaData))
    (hks2 : KsCtxAssumption root (alloc.vec.Vec Std.U8))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (hd : key.domain ≠ 3#i32) (g : database.KeyIdGuard) (entry : database.KeyEntry)
    (hload : loadKeyEntry loadCheck db key database.KeyType.Client
      database.KeyEntryLoadBits.BOTH caller_uid () = ok (.Ok (g, entry), db1))
    (blob : alloc.vec.Vec Std.U8 × database.BlobMetaData)
    (hblob : entry.key_blob_info = some blob) (hcert : entry.cert = none) :
    ∃ e, attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e, db1) ∧ root e = ErrRoot.ks invalidArgumentError := by
  sorry

/-- conditional: for a domain other than `BLOB`, if `load_key_entry` returns an entry with a key
blob `(blob, bmeta)` and a certificate `cert`, the result is `Ok (g, blob, cert, bmeta)`, with the
guard `g` of the entry, and the database that `load_key_entry` returned. The entry is consumed.
Hypotheses: the outcome of `load_key_entry`; `format` and `from_str_nonconst` do not fail; the
assumptions of `context` for an `anyhow::Error` (`AnyCtxLaw`) and for a keystore2 error
(`KsCtxAssumption`),
at the three success types of the three calls. -/
theorem load_attest_key_blob_and_cert_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8 × database.BlobMetaData))
    (hks2 : KsCtxAssumption root (alloc.vec.Vec Std.U8))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (hd : key.domain ≠ 3#i32) (g : database.KeyIdGuard) (entry : database.KeyEntry)
    (hload : loadKeyEntry loadCheck db key database.KeyType.Client
      database.KeyEntryLoadBits.BOTH caller_uid () = ok (.Ok (g, entry), db1))
    (blob : alloc.vec.Vec Std.U8) (bmeta : database.BlobMetaData)
    (cert : alloc.vec.Vec Std.U8)
    (hblob : entry.key_blob_info = some (blob, bmeta)) (hcert : entry.cert = some cert) :
    attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
      ok (.Ok (g, blob, cert, bmeta), db1) := by
  sorry
