import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath
open std.fs.ReadDir.Insts renaming
  CoreIterTraitsIteratorIteratorResultDirEntryError.next → readDirNext

/-- conditional: if the directory of the user is read, and its entries are the directory entries
`entries` (none of them an error), `list_user` returns the names of the entries, in the order of
`next`, without the entries whose name is not valid UTF-8. `nm d` is the name that the calls on
the entry `d` return, `none` for a name that is not valid UTF-8. Hypotheses: the outcome of
`make_user_path_name`; `as_path` of the path and the call `fs::read_dir` that the retry loop
makes, which returns `Ok dir` (the statement covers a run whose first call is not interrupted);
the whole sequence of results of `next`; the calls that give the name of each entry; the
assumption about `to_string` of a `&str`; the assumption that a successful `OsStr::to_str`
returns valid UTF-8; the `context` assumption for an `io::Error`; the message assumptions; and
that the list has at most `Usize.max` names. -/
theorem list_user_ok (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.DirEntry) (hts : StrToStringSpec) (hto : OsStrToStrSpec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (dir : std.fs.ReadDir)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Ok dir))
    (entries : List std.fs.DirEntry)
    (hrun : NextRun readDirNext dir (entries.map okEntry))
    (nm : std.fs.DirEntry → Option Str) (hnm : ∀ d ∈ entries, FileNameIs d (nm d))
    (hlen : (entries.filterMap nm).length ≤ Std.Usize.max) :
    ∃ v, list_user self user = ok (.Ok v) ∧
      v.val.map utf8Bytes = (entries.filterMap nm).map (·.val) := by
  sorry

/-- conditional: if the directory of the user is read, the entries `pre` (none of them an error) are
followed by an entry that is the error `e`, `list_user` returns an error whose root cause is an
`io::Error` (class `other`). The names read before the error are dropped. In the Rust source the
function returns at the error, so the iterator is not called again and nothing is assumed about
what it would yield. Hypotheses: those of `list_user_ok`, with the calls of `next` for `pre`
(`NextPrefix`, which leaves the iterator `dir1`), one call of `next` on `dir1` that returns `Err
e`, and a call of each entry of `pre` that returns a name. -/
theorem list_user_entry_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : IoErrCtxLaw root std.fs.DirEntry) (hts : StrToStringSpec) (hto : OsStrToStrSpec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (dir : std.fs.ReadDir)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Ok dir))
    (pre : List std.fs.DirEntry) (dir1 dir2 : std.fs.ReadDir) (e : IoError)
    (hpre : NextPrefix readDirNext dir (pre.map okEntry) dir1)
    (hn : readDirNext dir1 = ok (some (.Err e), dir2))
    (hnm : ∀ d ∈ pre, ∃ o, FileNameIs d o) (hlen : pre.length ≤ Std.Usize.max) :
    ∃ e', list_user self user = ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

/-- conditional: if reading the directory of the user returns an error `e` of the kind `NotFound`,
`list_user` returns `Ok` of the empty list. Hypotheses: the outcome of `make_user_path_name`;
`as_path` of the path; the call `fs::read_dir` returns `Err e`; the kind of `e` is `NotFound`;
and the assumption about `default` of a vector of strings. -/
theorem list_user_not_found (hdef : VecStringDefaultSpec)
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (e : IoError)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Err e))
    (hk : ioErrorKind e = ok ioNotFound) :
    ∃ v, list_user self user = ok (.Ok v) ∧ v.val = [] := by
  sorry

/-- conditional: if reading the directory of the user returns an error `e` of a kind other than
`NotFound`, `list_user` returns an error whose root cause is an `io::Error` (class `other`).
Hypotheses: the outcome of `make_user_path_name`; `as_path` of the path; the call `fs::read_dir`
that the retry loop makes returns `Err e`; the kind `k` of `e` is neither `NotFound` nor
`Interrupted`; the `context` assumption for an `io::Error`; and the assumption about `format`. -/
theorem list_user_open_err (root : anyhow.Error → ErrRoot) (hfmt : AllocFmtFormatSpec)
    (hctx : IoErrCtxLaw root (alloc.vec.Vec String))
    (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) (path : std.path.PathBuf)
    (hp : make_user_path_name self user = ok path) (e : IoError)
    (q : std.path.Path) (hasp : pathBufAsPath path = ok q)
    (hr : readDirCall q = ok (.Err e))
    (k : IoErrorKind) (hk : ioErrorKind e = ok k)
    (hne : k ≠ ioNotFound) (hni : k ≠ ioInterrupted) :
    ∃ e', list_user self user = ok (.Err e') ∧ root e' = ErrRoot.other := by
  sorry

end Keystore2Verify.LegacyBlob
