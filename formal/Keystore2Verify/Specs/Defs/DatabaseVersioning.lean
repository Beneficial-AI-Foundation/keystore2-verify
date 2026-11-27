import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `database/versioning.rs`

`update_version` adds a context to the error of a `rusqlite` call. The definitions below name
that call of `context` as an instance of the shared assumption, and the arguments of the SQL
call. Nothing here is an axiom.
-/

namespace Keystore2Verify.DatabaseVersioning
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.result.Result.Insts.AnyhowContext
open anyhow.context.ext.StdError
open rusqlite.error.Error.Insts renaming CoreErrorError → rusqliteErrorError

/-- The shared assumption about an external function, `ResultContextLaw`, for the call
`Result::context` on the result of `Connection::execute`: an `Ok n` stays `Ok n`, and an
`Err x` of `rusqlite::Error` becomes an error whose root class is `rootSql x`. The classifier
`rootSql` is a parameter: a `rusqlite::Error` can wrap another error (for example a boxed
conversion failure), so its class is not fixed. The message type is `&str`. -/
abbrev RusqliteCtxLaw (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw rootSql root
    (context (T := Std.Usize) (Blanket rusqliteErrorError)
      (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay))

/-- The parameters of the SQL call in `update_version`: the one value `new_version`. -/
noncomputable def updateParams (new_version : Std.U32) :=
  Array.to_slice (Array.make 1#usize [Dyn.mk _ U32.Insts.RusqliteTypesTo_sqlToSql new_version])

/-- The call of `Connection::execute` in `update_version`, on the connection `c`. -/
noncomputable def updateExecute (c : rusqlite.Connection) (new_version : Std.U32) :=
  rusqlite.Connection.execute Shared0SliceShared1P.Insts.RusqliteParamsParams c
    (toStr "UPDATE persistent.version SET version = ? WHERE id = 0;") (updateParams new_version)

end Keystore2Verify.DatabaseVersioning
