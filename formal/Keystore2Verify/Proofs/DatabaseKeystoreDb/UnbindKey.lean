import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.ops.function renaming Fn → FnTrait
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.unbind_key.closure.Insts renaming
  CoreOpsFunctionFnTupleShared4TransactionResultPairBoolTupleError → unbindFn

/-- conditional: the result is the outcome of the transaction, with the context message added to an
error. The database is the one that `with_transaction` returns. If the transaction returns `Ok ()`
the result is `Ok ()`. If it returns `Err e` the result is an `Err e'` with the same root cause
as `e`. The transaction is run in the immediate mode `TX_unbind_key` on the tuple of the key
descriptor, the key type, the caller uid and the callback `check_permission`. In the Rust source
the transaction closure checks the permission before it removes any row; no statement here can say
that, as `with_transaction` is not translated. Hypotheses: `watch` returns; `with_transaction`
returns `(r, self1)`; `format` and `from_str_nonconst` do not panic; the `context` assumption for
`anyhow::Error`. -/
theorem unbind_key_transaction (root : anyhow.Error → ErrRoot) {T0 : Type _}
    (inst : FnTrait T0
      (KeyDesc × Option permission.KeyPermSet)
      (core.result.Result Unit anyhow.Error))
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (caller_uid : utils.AppUid) (check_permission : T0)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result Unit anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::unbind_key") = ok w)
    (hwt : database.KeystoreDB.with_transaction (unbindFn inst) self
      (database.TransactionBehavior.Immediate (toStr "TX_unbind_key"))
      (key, key_type, caller_uid, check_permission) = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root Unit) :
    ∃ r1, database.KeystoreDB.unbind_key inst self key key_type caller_uid check_permission =
        ok (r1, self1) ∧ ContextOutcome root r r1 := by
  sorry
