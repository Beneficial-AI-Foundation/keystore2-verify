import Keystore2Verify.Proofs.AttestationKeyUtils.GetUserGeneratedAttestationKey
import Keystore2Verify.Proofs.AttestationKeyUtils.LoadAttestKeyBlobAndCert

namespace Keystore2Verify.AttestationKeyUtils

section GetUserGeneratedAttestationKey
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open attestation_key_utils renaming load_attest_key_blob_and_cert → loadAttest

recall get_user_generated_attestation_key_load_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 ×
      database.BlobMetaData))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (e : anyhow.Error) (hload : loadAttest key caller_uid db = ok (.Err e, db1)) :
    ∃ e', attestation_key_utils.get_user_generated_attestation_key key caller_uid db =
        ok (.Err e', db1) ∧ root e' = root e

recall get_user_generated_attestation_key_parse_err (root : anyhow.Error → ErrRoot)
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
        ok (.Err e, db1) ∧ root e = ErrRoot.crypto ce

recall get_user_generated_attestation_key_ok (root : anyhow.Error → ErrRoot)
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
        db1)

end GetUserGeneratedAttestationKey

section LoadAttestKeyBlobAndCert
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals Keystore2Verify.Permission
open android_system_keystore2.aidl.android.system.keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open attestation_key_utils.load_attest_key_blob_and_cert.closure.Insts
  renaming CoreOpsFunctionFnPairShared0KeyDescriptorOptionKeyPermSetResultTupleError → loadCheck
open database.KeystoreDB renaming load_key_entry → loadKeyEntry

recall load_attest_key_blob_and_cert_blob (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsCtxAssumption root Loaded) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.INVALID_ARGUMENT = ok ec)
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db : database.KeystoreDB)
    (hd : key.domain = 3#i32) :
    ∃ e, attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e, db) ∧ root e = ErrRoot.ks (error.Error.Km ec)

recall load_attest_key_blob_and_cert_load_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (hd : key.domain ≠ 3#i32) (e : anyhow.Error)
    (hload : loadKeyEntry loadCheck db key database.KeyType.Client
      database.KeyEntryLoadBits.BOTH caller_uid () = ok (.Err e, db1)) :
    ∃ e', attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e', db1) ∧ root e' = root e

recall load_attest_key_blob_and_cert_no_blob (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8 × database.BlobMetaData))
    (key : KeyDescriptor.KeyDescriptor) (caller_uid : utils.AppUid) (db db1 : database.KeystoreDB)
    (hd : key.domain ≠ 3#i32) (g : database.KeyIdGuard) (entry : database.KeyEntry)
    (hload : loadKeyEntry loadCheck db key database.KeyType.Client
      database.KeyEntryLoadBits.BOTH caller_uid () = ok (.Ok (g, entry), db1))
    (hblob : entry.key_blob_info = none) :
    ∃ e, attestation_key_utils.load_attest_key_blob_and_cert key caller_uid db =
        ok (.Err e, db1) ∧ root e = ErrRoot.ks invalidArgumentError

recall load_attest_key_blob_and_cert_no_cert (root : anyhow.Error → ErrRoot)
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
        ok (.Err e, db1) ∧ root e = ErrRoot.ks invalidArgumentError

recall load_attest_key_blob_and_cert_ok (root : anyhow.Error → ErrRoot)
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
      ok (.Ok (g, blob, cert, bmeta), db1)

end LoadAttestKeyBlobAndCert

end Keystore2Verify.AttestationKeyUtils
