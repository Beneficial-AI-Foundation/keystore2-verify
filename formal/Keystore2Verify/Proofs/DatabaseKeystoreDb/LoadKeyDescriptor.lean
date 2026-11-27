import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.load_key_descriptor.closure.Insts renaming
  CoreOpsFunctionFnTupleShared1TransactionResultPairBoolOptionKeyDescriptorError → descriptorFn

/-- conditional: the result is the outcome of the transaction, with the context message added to
an error. The database is the one that `with_transaction` returns. If the transaction returns
`Ok x` (some descriptor, or none for a key id with no row) the result is the same `Ok x`. If it
returns `Err e` the result is an `Err e'` with the same root cause as `e`. The transaction is
run in the deferred mode on the key id. In the Rust source the closure reads the domain, the
namespace and the alias, and the blob of the descriptor is always none; no statement here can say
that, as `with_transaction` is not translated. Hypotheses: `watch` returns; `with_transaction`
returns `(r, self1)`; `format` and `from_str_nonconst` do not panic; the `context` assumption for
`anyhow::Error`. -/
theorem load_key_descriptor_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (key_id : Std.I64)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result (Option KeyDesc) anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::load_key_descriptor") = ok w)
    (hwt : database.KeystoreDB.with_transaction descriptorFn self
      database.TransactionBehavior.Deferred key_id = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root (Option KeyDesc)) :
    ∃ r1, database.KeystoreDB.load_key_descriptor self key_id = ok (r1, self1) ∧
      ContextOutcome root r r1 := by
  sorry
