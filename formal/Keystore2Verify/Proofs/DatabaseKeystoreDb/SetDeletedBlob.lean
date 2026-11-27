import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.KeystoreDB.set_deleted_blob.closure.Insts renaming
  CoreOpsFunctionFnTupleShared2TransactionResultPairBoolTupleError → deletedBlobFn

/-- conditional: the result is the outcome of the transaction, with the context message added to an
error. The database is the one that `with_transaction` returns. If the transaction returns `Ok x`
the result is the same `Ok x`. If it returns `Err e` the result is an `Err e'` with the same root
cause as `e`. Hypotheses: `watch` returns; `with_transaction`, run in the immediate mode
`TX_set_deleted_blob` on the pair (`blob`, `blob_metadata`), returns `(r, self1)`; `format` and
`from_str_nonconst` do not panic; the `context` assumption for `anyhow::Error`. In the Rust source
the transaction closure stores the blob under the key id `-1`; no statement here can say that, as
`with_transaction` is not translated. -/
theorem set_deleted_blob_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (blob : Slice Std.U8) (blob_metadata : database.BlobMetaData)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result Unit anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::set_deleted_blob") = ok w)
    (hwt : database.KeystoreDB.with_transaction deletedBlobFn self
      (database.TransactionBehavior.Immediate (toStr "TX_set_deleted_blob"))
      (blob, blob_metadata) = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root Unit) :
    ∃ r1, database.KeystoreDB.set_deleted_blob self blob blob_metadata = ok (r1, self1) ∧
      ContextOutcome root r r1 := by
  sorry
