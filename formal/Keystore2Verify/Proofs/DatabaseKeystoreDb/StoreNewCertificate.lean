import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.store_new_certificate.closure.Insts renaming
  CoreOpsFunctionFnTupleShared6TransactionResultPairBoolKeyIdGuardError → newCertFn
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
  renaming INVALID_ARGUMENT → invalidArgument

/-! The check of the descriptor is the one of `store_new_key`: an alias, the domain `APP` (0) or
`SELINUX` (2), and no blob. Every other descriptor returns the same error before the transaction
starts. As in that function, no theorem can say which steps of the transaction closure run (among
them the creation date, which is read from the clock), because `with_transaction` is not
translated. -/

/-- conditional: a descriptor without an alias is rejected. The result is an `Err` whose root cause
is the keystore2 error `Rc INVALID_ARGUMENT`, and the database is returned unchanged. In the
Rust source this path returns before `with_transaction` is called. Hypotheses: `watch` returns;
`format` and `from_str_nonconst` do not panic; the `context` assumption for a keystore2 error. -/
theorem store_new_certificate_no_alias (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = none)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument) := by
  sorry

/-- conditional: a descriptor with an alias and a domain that is neither `APP` (0) nor `SELINUX`
(2) is rejected, with the same result as in `store_new_certificate_no_alias`. Hypotheses as
there. -/
theorem store_new_certificate_bad_domain (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = some a) (h0 : key.domain ≠ 0#i32) (h2 : key.domain ≠ 2#i32)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument) := by
  sorry

/-- conditional: a descriptor with an alias and the domain `APP` (0) or `SELINUX` (2), but with a
blob, is rejected, with the same result as in `store_new_certificate_no_alias`. Hypotheses as
there. -/
theorem store_new_certificate_has_blob (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid) (a : String)
    (b : alloc.vec.Vec Std.U8) (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = some b)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument) := by
  sorry

/-- conditional: an accepted descriptor (alias `a`, domain `APP` or `SELINUX`, no blob). The
result is the outcome of the transaction, with a context message added to an error. The database is
the one that `with_transaction` returns. If the transaction returns `Ok x` the result is the
same `Ok x`. If it returns `Err e` the result is an `Err e'` with the same root cause as `e`.
The transaction is run in the immediate mode `TX_store_new_certificate` on the tuple of the
domain, the namespace, the key type, the uuid, the certificate and the alias. Hypotheses: `watch`
returns; `with_transaction` returns `(r, self1)`; `format` and `from_str_nonconst` do not panic;
the `context` assumption for `anyhow::Error`. -/
theorem store_new_certificate_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result database.KeyIdGuard anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = none)
    (hwt : database.KeystoreDB.with_transaction newCertFn self
      (database.TransactionBehavior.Immediate (toStr "TX_store_new_certificate"))
      (key.domain, key.nspace, key_type, km_uuid, cert, a) = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root database.KeyIdGuard) :
    ∃ r1, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (r1, self1) ∧ ContextOutcome root r r1 := by
  sorry
