import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath

/-- conditional: if the alias has a known keystore prefix, `remove_legacy_keystore_entry` returns
`Ok false`. In the Rust source this path returns before any file is touched. Hypothesis: the
outcome of `make_legacy_keystore_entry_filename`. -/
theorem remove_legacy_keystore_entry_prefixed (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (al : Str)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok none) :
    remove_legacy_keystore_entry self uid al = ok (.Ok false) := by
  sorry

/-- conditional: if the file is removed and the empty-directory step succeeds,
`remove_legacy_keystore_entry` returns `Ok true`. Hypotheses: the outcome of
`make_legacy_keystore_entry_filename`; `as_path` of the path, and the call `fs::remove_file`
that the retry loop makes, which returns `Ok` (the statement covers a run whose first call is
not interrupted); the outcome of `owning_user` and of `remove_user_dir_if_empty`; the `context`
assumption for an `anyhow::Error`; and the assumption about `format`. -/
theorem remove_legacy_keystore_entry_removed (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : AnyCtxLaw root Unit)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (path : std.path.PathBuf) (q : std.path.Path) (r : Unit) (user : utils.AndroidUserId)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Ok r))
    (hu : utils.AppUid.owning_user uid = ok user)
    (hdir : remove_user_dir_if_empty self user = ok (.Ok ())) :
    remove_legacy_keystore_entry self uid al = ok (.Ok true) := by
  sorry

/-- conditional: if the file is removed and `remove_user_dir_if_empty` returns an error `e`,
`remove_legacy_keystore_entry` returns an error with the same root cause. The file is already
removed. Hypotheses: those of `remove_legacy_keystore_entry_removed`, with the outcome `Err e`. -/
theorem remove_legacy_keystore_entry_dir_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : AnyCtxLaw root Unit)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (path : std.path.PathBuf) (q : std.path.Path) (r : Unit) (user : utils.AndroidUserId)
    (e : anyhow.Error)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Ok r))
    (hu : utils.AppUid.owning_user uid = ok user)
    (hdir : remove_user_dir_if_empty self user = ok (.Err e)) :
    ∃ e', remove_legacy_keystore_entry self uid al = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the removal fails with an error `e` of the kind `NotFound`,
`remove_legacy_keystore_entry` returns `Ok false`. In the Rust source this path does not touch
the user directory. Hypotheses: the outcome of `make_legacy_keystore_entry_filename`; `as_path`;
the call `fs::remove_file` returns `Err e`; the kind of `e` is `NotFound` (so the retry loop
does not repeat the call). -/
theorem remove_legacy_keystore_entry_not_found (self : legacy_blob.LegacyBlobLoader)
    (uid : utils.AppUid) (al : Str) (path : std.path.PathBuf) (q : std.path.Path) (e : IoError)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Err e))
    (hk : ioErrorKind e = ok ioNotFound) :
    remove_legacy_keystore_entry self uid al = ok (.Ok false) := by
  sorry

/-- conditional: if the removal fails with an error `e` of a kind other than `NotFound`,
`remove_legacy_keystore_entry` returns an error whose root cause is an `io::Error` (class
`other`). In the Rust source this path does not touch the user directory. Hypotheses: those of
`remove_legacy_keystore_entry_not_found`, with the kind of `e` any kind other than `NotFound`
and `Interrupted`; the `context` assumption for an `io::Error`; and the message assumptions. -/
theorem remove_legacy_keystore_entry_io_err (root : anyhow.Error → ErrRoot)
    (hmsg : MessageSpecs) (hctx : IoErrCtxLaw root Bool)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (path : std.path.PathBuf) (q : std.path.Path) (e : IoError)
    (k : IoErrorKind)
    (hfn : make_legacy_keystore_entry_filename self uid al = ok (some path))
    (hasp : pathBufAsPath path = ok q) (hrm : removeFileCall q = ok (.Err e))
    (hk : ioErrorKind e = ok k) (hne : k ≠ ioNotFound) (hni : k ≠ ioInterrupted) :
    ∃ e', remove_legacy_keystore_entry self uid al = ok (.Err e') ∧
      root e' = ErrRoot.other := by
  sorry

end Keystore2Verify.LegacyBlob
