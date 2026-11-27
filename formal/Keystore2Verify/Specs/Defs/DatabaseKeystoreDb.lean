import Keystore2Verify.Specs.Defs.Externals
import Keystore2Verify.Specs.Defs.Permission

/-! # Definitions for the statements about `KeystoreDB` (second half of `database.rs`)

The context assumptions at the `context` calls of these methods, three new assumptions about
external functions, and the table names that `get_storage_stat` asks for. Nothing here is an axiom.

The methods reach SQLite only through `rusqlite` functions and through `KeystoreDB` helpers that the
translation could not extract. Their outcomes are inline hypotheses of the theorems. -/

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay
open alloc.string.String.Insts renaming CoreFmtDebug → StringDebug
open error.Error.Insts renaming CoreErrorError → KsErrorError
open rusqlite.error.Error.Insts renaming CoreErrorError → RusqliteErrorError
open anyhow.context.ext.StdError renaming Blanket → StdBlanket
open core.result.Result.Insts.AnyhowContext
open Keystore2Verify.Externals
open anyhow.error.Error renaming msg → errorMsg
open std.path.Path renaming to_path_buf → pathToPathBuf
open std.path.Path renaming to_string_lossy → pathToStringLossy
open std.path.PathBuf renaming push → pathBufPush
open std.path.PathBuf.Insts.CoreOpsDerefDerefPath renaming deref → pathBufDeref
open alloc.borrow.Cow.Insts.CoreOpsDerefDeref renaming deref → cowDeref
open Str.Insts.AllocBorrowToOwnedString renaming to_owned → strToOwned
open alloc.string.String renaming push_str → stringPushStr

/-! ## The `context` calls with a standard error type

`Externals.lean` has the assumption for a call on an `anyhow::Error` (`AnyCtxLaw`). The two other
kinds of call in these methods start from a keystore2 error or from a `rusqlite` error. -/

/-- A call `Err(keystore2_error).context(s)` with a `String` message, on a result that holds a
`T`. The root cause of the new error is the keystore2 error. -/
abbrev KsErrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun x => ErrRoot.ks x) root
    (context (T := T) (StdBlanket KsErrorError) StringDisplay)

/-- A call `r.context(s)` with a `String` message, on a result that holds a `rusqlite::Error` and
a `T`. `rootSql` classifies the root cause of a `rusqlite` error. The root cause of the new error is
the root cause of the `rusqlite` error, whatever error it wraps. -/
abbrev RusqliteCtxLaw (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (T : Type) : Prop :=
  ResultContextLaw rootSql root
    (context (T := T) (StdBlanket RusqliteErrorError) StringDisplay)

/-- What a `.context(..)` call does to a result `r` of type `Result<T, anyhow::Error>`: an `Ok`
stays the same `Ok`, and an `Err` becomes an `Err` with the same root cause. `r1` is the result
after the call. -/
def ContextOutcome {T : Type} (root : anyhow.Error → ErrRoot)
    (r r1 : core.result.Result T anyhow.Error) : Prop :=
  (∀ x, r = .Ok x → r1 = .Ok x) ∧
  (∀ e, r = .Err e → ∃ e', r1 = .Err e' ∧ root e' = root e)

/-! ## The path of the persistent database -/

/-- The lossy string form of `db_root` joined with `persistent.sqlite`, as the path functions give
it: `to_path_buf`, `push`, `deref`, `to_string_lossy` and the `deref` of the `Cow`. These are the
calls of `make_persistent_path` before the string `"file:"` is extended. -/
noncomputable def persistentPathLossy (db_root : std.path.Path) : Result Str := do
  let pb ← pathToPathBuf db_root
  let pb1 ←
    pathBufPush (Shared0T.Insts.CoreConvertAsRef Str.Insts.CoreConvertAsRefPath) pb
      database.KeystoreDB.PERSISTENT_DB_FILENAME
  let p ← pathBufDeref pb1
  let c ← pathToStringLossy p
  cowDeref Str.Insts.AllocBorrowToOwnedString c

/-! ## New assumptions about external functions -/

/-- Assumption about an external function: `str::to_owned` (register record
`ks2-ext-str-insts-allocborrowtoownedstring-to-owned`).
`to_owned` of the view of `"file:"` never panics and returns the string `"file:"`. Nothing is
said for other strings. Idealisation: allocation never fails. -/
def StrToOwnedSpec : Prop :=
  strToOwned (toStr "file:") = ok "file:"

/-- Assumption about an external function: `String::push_str` (register record
`ks2-ext-alloc-string-string-push-str`).
`push_str "file:" (view of u)` never panics and returns `"file:" ++ u`. Nothing is said for other
starting strings. Idealisation: allocation never fails. -/
def StringPushStrSpec : Prop :=
  ∀ (u : String) (h : u.toByteArray.size ≤ U32.max),
    stringPushStr "file:" (toStr u h) = ok ("file:" ++ u)

/-- Assumption about an external function: `anyhow::Error::msg` at the type `String` (register
record `ks2-ext-anyhow-error-error-msg`).
`msg s` never panics. The error it returns has a root cause that is a plain message, which is of
class `other` for the classifier `root`. Nothing is said about the message text.
Idealisation: allocation never fails. -/
def AnyhowErrorMsgSpec (root : anyhow.Error → ErrRoot) : Prop :=
  ∀ s : String, ∃ e, errorMsg StringDisplay StringDebug s = ok e ∧
    root e = ErrRoot.other

/-! ## Blobs -/

/-- The result of `load_blob_components`: whether the entry has a key blob, the key blob with its
metadata, the certificate, and the certificate chain. -/
abbrev BlobComponents : Type :=
  Bool × Option (alloc.vec.Vec Std.U8 × database.BlobMetaData) × Option (alloc.vec.Vec Std.U8) ×
    Option (alloc.vec.Vec Std.U8)

/-! ## Storage types -/

/-- The table or index that `get_storage_stat` asks about for the storage type with the number
`n` (the AIDL values of `Storage`). `none` for `DATABASE` (15), `AUTH_TOKEN` (11) and every number
that is not a supported storage type. -/
def storageTableName : Int → Option Str
  | 1 => some (toStr "keyentry")
  | 2 => some (toStr "keyentry_id_index")
  | 3 => some (toStr "keyentry_domain_namespace_index")
  | 4 => some (toStr "blobentry")
  | 5 => some (toStr "blobentry_keyentryid_index")
  | 6 => some (toStr "keyparameter")
  | 7 => some (toStr "keyparameter_keyentryid_index")
  | 8 => some (toStr "keymetadata")
  | 9 => some (toStr "keymetadata_keyentryid_index")
  | 10 => some (toStr "grant")
  | 12 => some (toStr "blobmetadata")
  | 13 => some (toStr "blobmetadata_blobentryid_index")
  | _ => none

/-- The number of `Storage::DATABASE`. -/
def storageDatabase : Int := 15

/-- The number of `Storage::AUTH_TOKEN`. -/
def storageAuthToken : Int := 11

end Keystore2Verify.DatabaseKeystoreDb
