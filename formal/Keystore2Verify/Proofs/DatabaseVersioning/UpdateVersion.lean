import Keystore2Verify.Specs.Defs.DatabaseVersioning

namespace Keystore2Verify.DatabaseVersioning
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open Aeneas.Std.core.fmt.Arguments renaming from_str → argumentsFromStr
open rusqlite.transaction.Transaction.Insts renaming CoreOpsDerefDerefConnection.deref → txDeref

/-- conditional: if the SQL update reports one changed row, `update_version` returns `ok (Ok ())`.
The database effect is not modelled: no statement says that the stored version changed.
Hypotheses: `RusqliteCtxLaw rootSql root`; `deref` of the transaction returns the connection
`c`; and `execute` returns `ok (Ok 1)`. -/
theorem update_version_one_row (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk 1#usize)) :
    database.versioning.update_version tx new_version = ok (ROk ()) := by
  sorry

/-- conditional: if the SQL update reports `n ≠ 1` changed rows, `update_version` returns an error
whose root class is that of the error `e` that the code builds from the text "In update_version:
No rows were updated.". Which class that is, and the message, are not stated. Hypotheses:
`RusqliteCtxLaw rootSql root`; `deref` returns the connection `c`; `execute` returns `ok (Ok n)`
with `n ≠ 1`; `from_str` returns `a`; `format_err a` returns `e0`; and `must_use e0` returns
`e`. -/
theorem update_version_no_row_updated (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (n : Std.Usize) (a : core.fmt.Arguments) (e0 e : anyhow.Error)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk n)) (hn : n ≠ 1#usize)
    (ha : argumentsFromStr (toStr "In update_version: No rows were updated.") = ok a)
    (hf : anyhow.__private.format_err a = ok e0) (hm : anyhow.__private.must_use e0 = ok e) :
    ∃ e', database.versioning.update_version tx new_version = ok (RErr e') ∧
      root e' = root e := by
  sorry

/-- conditional: if the SQL update reports `n ≠ 1` changed rows and `format_err` fails with `x`,
`update_version` fails with `x`. Hypotheses: `RusqliteCtxLaw rootSql root`; `deref` returns the
connection `c`; `execute` returns `ok (Ok n)` with `n ≠ 1`; `from_str` returns `a`; and
`format_err a` returns `fail x`. -/
theorem update_version_format_err_fails (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (n : Std.Usize) (a : core.fmt.Arguments) (x : Error)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk n)) (hn : n ≠ 1#usize)
    (ha : argumentsFromStr (toStr "In update_version: No rows were updated.") = ok a)
    (hf : anyhow.__private.format_err a = fail x) :
    database.versioning.update_version tx new_version = fail x := by
  sorry

/-- conditional: if the SQL update reports `n ≠ 1` changed rows and `must_use` fails with `x`,
`update_version` fails with `x`. Hypotheses: `RusqliteCtxLaw rootSql root`; `deref` returns the
connection `c`; `execute` returns `ok (Ok n)` with `n ≠ 1`; `from_str` returns `a`;
`format_err a` returns `e0`; and `must_use e0` returns `fail x`. -/
theorem update_version_must_use_fails (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (n : Std.Usize) (a : core.fmt.Arguments) (e0 : anyhow.Error) (x : Error)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk n)) (hn : n ≠ 1#usize)
    (ha : argumentsFromStr (toStr "In update_version: No rows were updated.") = ok a)
    (hf : anyhow.__private.format_err a = ok e0) (hm : anyhow.__private.must_use e0 = fail x) :
    database.versioning.update_version tx new_version = fail x := by
  sorry

/-- conditional: if the SQL call returns a `rusqlite::Error` `x`, `update_version` returns an
error whose root class is `rootSql x` (the `rusqlite` error with the context "In update_version:
Failed to update row."). Hypotheses: `RusqliteCtxLaw rootSql root`; `deref` returns the
connection `c`; and `execute` returns `ok (Err x)`. -/
theorem update_version_execute_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (x : rusqlite.error.Error) (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (RErr x)) :
    ∃ e, database.versioning.update_version tx new_version = ok (RErr e) ∧
      root e = rootSql x := by
  sorry

/-- conditional: if `deref` of the transaction fails with `e`, `update_version` fails with `e`.
Hypothesis: that call returns `fail e`. -/
theorem update_version_deref_fails (tx : rusqlite.transaction.Transaction) (new_version : Std.U32)
    (e : Error) (hd : txDeref tx = fail e) :
    database.versioning.update_version tx new_version = fail e := by
  sorry

/-- conditional: if `execute` fails with `e`, `update_version` fails with `e`. Hypotheses: `deref`
returns the connection `c`, and `execute` returns `fail e`. -/
theorem update_version_execute_fails (tx : rusqlite.transaction.Transaction)
    (new_version : Std.U32) (c : rusqlite.Connection) (e : Error)
    (hd : txDeref tx = ok c) (he : updateExecute c new_version = fail e) :
    database.versioning.update_version tx new_version = fail e := by
  sorry

end Keystore2Verify.DatabaseVersioning
