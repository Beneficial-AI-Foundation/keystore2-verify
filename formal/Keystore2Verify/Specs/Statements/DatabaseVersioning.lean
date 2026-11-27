import Keystore2Verify.Proofs.DatabaseVersioning.UpdateVersion

namespace Keystore2Verify.DatabaseVersioning

section UpdateVersion
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open Aeneas.Std.core.fmt.Arguments renaming from_str → argumentsFromStr
open rusqlite.transaction.Transaction.Insts renaming CoreOpsDerefDerefConnection.deref → txDeref

recall update_version_one_row (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk 1#usize)) :
    database.versioning.update_version tx new_version = ok (ROk ())

recall update_version_no_row_updated (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (n : Std.Usize) (a : core.fmt.Arguments) (e0 e : anyhow.Error)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk n)) (hn : n ≠ 1#usize)
    (ha : argumentsFromStr (toStr "In update_version: No rows were updated.") = ok a)
    (hf : anyhow.__private.format_err a = ok e0) (hm : anyhow.__private.must_use e0 = ok e) :
    ∃ e', database.versioning.update_version tx new_version = ok (RErr e') ∧
      root e' = root e

recall update_version_format_err_fails (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (n : Std.Usize) (a : core.fmt.Arguments) (x : Error)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk n)) (hn : n ≠ 1#usize)
    (ha : argumentsFromStr (toStr "In update_version: No rows were updated.") = ok a)
    (hf : anyhow.__private.format_err a = fail x) :
    database.versioning.update_version tx new_version = fail x

recall update_version_must_use_fails (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (n : Std.Usize) (a : core.fmt.Arguments) (e0 : anyhow.Error) (x : Error)
    (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (ROk n)) (hn : n ≠ 1#usize)
    (ha : argumentsFromStr (toStr "In update_version: No rows were updated.") = ok a)
    (hf : anyhow.__private.format_err a = ok e0) (hm : anyhow.__private.must_use e0 = fail x) :
    database.versioning.update_version tx new_version = fail x

recall update_version_execute_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (hCtx : RusqliteCtxLaw rootSql root)
    (tx : rusqlite.transaction.Transaction) (new_version : Std.U32) (c : rusqlite.Connection)
    (x : rusqlite.error.Error) (hd : txDeref tx = ok c)
    (he : updateExecute c new_version = ok (RErr x)) :
    ∃ e, database.versioning.update_version tx new_version = ok (RErr e) ∧
      root e = rootSql x

recall update_version_deref_fails (tx : rusqlite.transaction.Transaction) (new_version : Std.U32)
    (e : Error) (hd : txDeref tx = fail e) :
    database.versioning.update_version tx new_version = fail e

recall update_version_execute_fails (tx : rusqlite.transaction.Transaction)
    (new_version : Std.U32) (c : rusqlite.Connection) (e : Error)
    (hd : txDeref tx = ok c) (he : updateExecute c new_version = fail e) :
    database.versioning.update_version tx new_version = fail e

end UpdateVersion

end Keystore2Verify.DatabaseVersioning
