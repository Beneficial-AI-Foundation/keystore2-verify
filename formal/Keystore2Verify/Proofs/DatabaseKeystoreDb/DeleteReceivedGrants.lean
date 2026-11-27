import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open rusqlite.transaction.Transaction.Insts.CoreOpsDerefDerefConnection renaming deref → txDeref
open I32.Insts renaming RusqliteTypesTo_sqlToSql → i32ToSql

/-! In each theorem `s` is the query text that `format!` builds and `sv` its `&str` view. The
translation erases the formatting arguments, so the text itself is not modelled: `s` and `sv`
are only named, and `execute` is constrained at `sv` and nowhere else. The deletion of rows has no
effect that a statement can see: the model has no table state. -/

/-- conditional: if the statement runs and returns the number `n` of deleted rows, the result is `Ok
b` with `b` true exactly when `n` is not zero. Hypotheses: `deref` of the transaction returns the
connection `c`; the offset `AID_USER_OFFSET` evaluates; `format` does not panic
(`AllocFmtFormatSpec`, also used for the error message); `format` returns the query text `s`;
`deref` of `s` returns `sv`; `execute` on `c`, with the query `sv` and the single parameter `user`,
returns `Ok n`; the `context` assumption for a `rusqlite` error. -/
theorem delete_received_grants_deleted (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (user : utils.AndroidUserId)
    (c : rusqlite.Connection) (off : Std.U32) (n : Std.Usize)
    (hderef : txDeref tx = ok c)
    (hoff : utils.AID_USER_OFFSET = ok off)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hexec : rusqlite.Connection.execute
      Shared0SliceShared1P.Insts.RusqliteParamsParams c sv
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i32ToSql user ])) = ok (.Ok n))
    (hctx : RusqliteCtxLaw rootSql root Std.Usize) :
    ∃ b, database.KeystoreDB.delete_received_grants tx user = ok (.Ok b) ∧
      (b = true ↔ n.val ≠ 0) := by
  sorry

/-- conditional: if the statement returns an error, the result is an `Err e` whose root cause is the
root cause of the `rusqlite` error `x` (`rootSql x`), whatever error it wraps. Hypotheses as in
`delete_received_grants_deleted`, except that `execute` returns `Err x`. -/
theorem delete_received_grants_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (user : utils.AndroidUserId)
    (c : rusqlite.Connection) (off : Std.U32) (x : rusqlite.error.Error)
    (hderef : txDeref tx = ok c)
    (hoff : utils.AID_USER_OFFSET = ok off)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hexec : rusqlite.Connection.execute
      Shared0SliceShared1P.Insts.RusqliteParamsParams c sv
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i32ToSql user ])) = ok (.Err x))
    (hctx : RusqliteCtxLaw rootSql root Std.Usize) :
    ∃ e, database.KeystoreDB.delete_received_grants tx user = ok (.Err e) ∧
      root e = rootSql x := by
  sorry
