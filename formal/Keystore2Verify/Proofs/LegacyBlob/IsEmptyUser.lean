import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open std.fs.ReadDir.Insts.CoreIterTraitsIteratorIteratorResultDirEntryError renaming
  next → readDirNextFn
open std.path.Path renaming is_dir → pathIsDir
open std.path.PathBuf renaming as_path → pathBufAsPath

/-! In each theorem the function builds one path: `pathBufCloneFn` returns `p0` for the path of
the loader, the first `format` returns `s`, `pathPushString` returns `up` for `p0` and `s`, and
`as_path` returns `p` for `up`. The text of `s` (`user_` and the user number in the Rust source)
is not observable in the model. -/

/-- conditional: if that path is not a directory, `is_empty_user` returns `Ok true`. In the Rust
source this path returns before the directory is read. Hypotheses: the outcomes of the clone, of
`format`, of the push, of `as_path` and of `is_dir` on that path. -/
theorem is_empty_user_not_dir (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p0 : std.path.PathBuf) (s : String) (up : std.path.PathBuf) (p : std.path.Path)
    (hc : pathBufCloneFn self.path = ok p0) (hf : alloc.fmt.format () = ok s)
    (hpush : pathPushString p0 s = ok up) (hasp : pathBufAsPath up = ok p)
    (hdir : pathIsDir p = ok false) :
    is_empty_user self user = ok (.Ok true) := by
  sorry

/-- conditional: if that path is a directory and reading it returns `dir`, `is_empty_user` returns
`Ok true` exactly when the first call of `next` on `dir` returns `none`. An entry that is an
`Err` counts as an entry. Hypotheses: those of `is_empty_user_not_dir`, with `is_dir` returning
`true`; `pathBufDeref` of `up` returns `pd` and the call `Path::read_dir` that the retry loop
makes returns `Ok dir` (the statement covers a run whose first call is not interrupted); the
outcome of the first call of `next`; the `context` assumption for an `io::Error`; and the
message assumptions. -/
theorem is_empty_user_dir (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.ReadDir)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p0 : std.path.PathBuf) (s : String) (up : std.path.PathBuf) (p : std.path.Path)
    (hc : pathBufCloneFn self.path = ok p0) (hf : alloc.fmt.format () = ok s)
    (hpush : pathPushString p0 s = ok up) (hasp : pathBufAsPath up = ok p)
    (hdir : pathIsDir p = ok true) (pd : std.path.Path) (hdd : pathBufDeref up = ok pd)
    (dir : std.fs.ReadDir) (hrd : pathReadDirCall pd = ok (.Ok dir))
    (o : Option (core.result.Result std.fs.DirEntry IoError)) (dir' : std.fs.ReadDir)
    (hn : readDirNextFn dir = ok (o, dir')) :
    is_empty_user self user = ok (.Ok o.isNone) := by
  sorry

/-- conditional: if that path is a directory and reading it returns the error `e`, `is_empty_user`
returns an error whose root cause is an `io::Error` (class `other`). Hypotheses: those of
`is_empty_user_dir`, with the call `Path::read_dir` returning `Err e` whose kind `k` is not
`Interrupted`, and no call of `next`. -/
theorem is_empty_user_read_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.ReadDir)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p0 : std.path.PathBuf) (s : String) (up : std.path.PathBuf) (p : std.path.Path)
    (hc : pathBufCloneFn self.path = ok p0) (hf : alloc.fmt.format () = ok s)
    (hpush : pathPushString p0 s = ok up) (hasp : pathBufAsPath up = ok p)
    (hdir : pathIsDir p = ok true) (pd : std.path.Path) (hdd : pathBufDeref up = ok pd)
    (e : IoError) (hrd : pathReadDirCall pd = ok (.Err e)) (k : IoErrorKind)
    (hk : ioErrorKind e = ok k) (hni : k ≠ ioInterrupted) :
    ∃ e', is_empty_user self user = ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

end Keystore2Verify.LegacyBlob
