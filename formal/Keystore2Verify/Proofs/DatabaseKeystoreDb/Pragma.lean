import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open rusqlite.types.from_sql renaming FromSql → FromSqlTrait
open database.KeystoreDB.pragma.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0RowResultTError → pragmaRow

/-! In each theorem `s` is the query text that `format!` builds from `nm` and `sv` its `&str`
view. The translation erases the formatting arguments, so the text itself is not modelled: `s`
and `sv` are only named, and `query_row` is constrained at `sv` and nowhere else. The name is not
checked in any way. The database is returned unchanged. -/

/-- conditional: if the query returns the value `v`, the result is `Ok v` and the database is
returned unchanged. Hypotheses: `format` does not panic (`AllocFmtFormatSpec`) and returns the query
text `s`; `deref` of `s` returns `sv`; `query_row` on the connection of `self`, with the query `sv`,
no parameters and the row reader for the first column, returns `Ok v`; the `context` assumption for
a `rusqlite` error. -/
theorem pragma_value (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) {T : Type _}
    (inst : FromSqlTrait T) (self : database.KeystoreDB) (nm : Str)
    (v : T)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hquery : rusqlite.Connection.query_row Tuple.Insts.RusqliteParamsParams
      (pragmaRow inst) self.conn sv () () = ok (.Ok v))
    (hctx : RusqliteCtxLaw rootSql root T) :
    database.KeystoreDB.pragma inst self nm = ok (.Ok v, self) := by
  sorry

/-- conditional: if the query returns an error `x` (for example, the pragma has no value, or the
column cannot be read as a `T`), the result is an `Err e` whose root cause is the root cause of the
`rusqlite` error `x` (`rootSql x`), whatever error it wraps, and the database is returned unchanged.
Hypotheses as in `pragma_value`, except that `query_row` returns `Err x`. -/
theorem pragma_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) {T : Type _}
    (inst : FromSqlTrait T) (self : database.KeystoreDB) (nm : Str)
    (x : rusqlite.error.Error)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hquery : rusqlite.Connection.query_row Tuple.Insts.RusqliteParamsParams
      (pragmaRow inst) self.conn sv () () = ok (.Err x))
    (hctx : RusqliteCtxLaw rootSql root T) :
    ∃ e, database.KeystoreDB.pragma inst self nm = ok (.Err e, self) ∧
      root e = rootSql x := by
  sorry
