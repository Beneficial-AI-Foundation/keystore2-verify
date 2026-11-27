import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.store_new_key.closure.Insts renaming
  CoreOpsFunctionFnTupleShared10TransactionResultPairBoolKeyIdGuardError → newKeyFn
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
  renaming INVALID_ARGUMENT → invalidArgument

/-! In the Rust source the descriptor is accepted when it has an alias, the domain is `APP` (0) or
`SELINUX` (2), and it has no blob. Every other descriptor returns the same error before the
transaction starts. The Rust source tests the three conditions in one `match`, so no result
depends on their order. The theorems
about the three kinds of rejected descriptor assume the `context` assumption for a keystore2 error.
The transaction closure is not translated into a statement of its own: `with_transaction` is not
translated, so no theorem here can say which steps of the closure run. -/

/-- conditional: a descriptor without an alias is rejected. The result is an `Err` whose root cause
is the keystore2 error `Rc INVALID_ARGUMENT`, and the database is returned unchanged. In the
Rust source this path returns before `with_transaction` is called. Hypotheses: `watch` returns;
`format` and `from_str_nonconst` do not panic; the `context` assumption for a keystore2 error. -/
theorem store_new_key_no_alias (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = none)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument) := by
  sorry

/-- conditional: a descriptor with an alias and a domain that is neither `APP` (0) nor `SELINUX`
(2) is rejected, with the same result as in `store_new_key_no_alias`. The blob of the descriptor
does not matter. Hypotheses as in `store_new_key_no_alias`. -/
theorem store_new_key_bad_domain (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = some a) (h0 : key.domain ≠ 0#i32) (h2 : key.domain ≠ 2#i32)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument) := by
  sorry

/-- conditional: a descriptor with an alias and the domain `APP` (0) or `SELINUX` (2), but with a
blob, is rejected, with the same result as in `store_new_key_no_alias`. Hypotheses as in
`store_new_key_no_alias`. -/
theorem store_new_key_has_blob (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid) (a : String)
    (b : alloc.vec.Vec Std.U8) (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = some b)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument) := by
  sorry

/-- conditional: an accepted descriptor (alias `a`, domain `APP` or `SELINUX`, no blob). The
result is the outcome of the transaction, with a context message added to an error. The database is
the one that `with_transaction` returns. If the transaction returns `Ok x` the result is the
same `Ok x`. If it returns `Err e` the result is an `Err e'` with the same root cause as `e`.
The transaction is run in the immediate mode `TX_store_new_key` on the tuple of the domain, the
namespace, the key type, the uuid, the blob and certificate information, the parameters, the
metadata and the alias. Hypotheses: `watch` returns; `with_transaction` returns `(r, self1)`;
`format` and `from_str_nonconst` do not panic; the `context` assumption for `anyhow::Error`. -/
theorem store_new_key_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result database.KeyIdGuard anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = none)
    (hwt : database.KeystoreDB.with_transaction newKeyFn self
      (database.TransactionBehavior.Immediate (toStr "TX_store_new_key"))
      (key.domain, key.nspace, key_type, km_uuid, blob_info, cert_info, params, metadata, a) =
        ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root database.KeyIdGuard) :
    ∃ r1, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (r1, self1) ∧ ContextOutcome root r r1 := by
  sorry
