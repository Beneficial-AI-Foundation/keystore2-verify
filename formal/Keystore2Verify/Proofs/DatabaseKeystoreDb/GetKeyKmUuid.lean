import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open rusqlite.transaction.Transaction.Insts.CoreOpsDerefDerefConnection renaming deref → txDeref
open I64.Insts renaming RusqliteTypesTo_sqlToSql → i64ToSql
open database.KeystoreDB.get_key_km_uuid.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0RowResultUuidError → kmUuidRow

/-- conditional: if the query on the `km_uuid` column of the key entry `key_id` returns the
uuid `u`, the result is `Ok u`. Hypotheses: `deref` of the transaction returns the connection
`c`; `query_row` on `c`, with the single parameter `key_id`, returns `Ok u`; `format` and
`from_str_nonconst` do not panic; the `context` assumption for a `rusqlite` error. -/
theorem get_key_km_uuid_found (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (key_id : Std.I64) (c : rusqlite.Connection)
    (u : database.Uuid)
    (hderef : txDeref tx = ok c)
    (hquery : rusqlite.Connection.query_row Shared0SliceShared1P.Insts.RusqliteParamsParams
      kmUuidRow c (toStr "SELECT km_uuid FROM persistent.keyentry WHERE id = ?")
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i64ToSql key_id ])) () = ok (.Ok u))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : RusqliteCtxLaw rootSql root database.Uuid) :
    database.KeystoreDB.get_key_km_uuid tx key_id = ok (.Ok u) := by
  sorry

/-- conditional: if the query returns an error `x` (for example, no row has this key id, or the
column cannot be read as a uuid), the result is an `Err e` whose root cause is the root cause of the
`rusqlite` error `x` (`rootSql x`), whatever error it wraps. Hypotheses as in
`get_key_km_uuid_found`, except that `query_row` returns `Err x`. -/
theorem get_key_km_uuid_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (key_id : Std.I64) (c : rusqlite.Connection)
    (x : rusqlite.error.Error)
    (hderef : txDeref tx = ok c)
    (hquery : rusqlite.Connection.query_row Shared0SliceShared1P.Insts.RusqliteParamsParams
      kmUuidRow c (toStr "SELECT km_uuid FROM persistent.keyentry WHERE id = ?")
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i64ToSql key_id ])) () = ok (.Err x))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : RusqliteCtxLaw rootSql root database.Uuid) :
    ∃ e, database.KeystoreDB.get_key_km_uuid tx key_id = ok (.Err e) ∧
      root e = rootSql x := by
  sorry
