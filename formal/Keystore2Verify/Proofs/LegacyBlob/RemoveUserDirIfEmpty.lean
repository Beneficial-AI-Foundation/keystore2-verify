import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath

/-- conditional: if the user directory is empty, `remove_user_dir_if_empty` tries to remove it and
returns `Ok ()`, whatever the removal returns. Hypotheses: `is_empty_user` returns `Ok true`;
`make_user_path_name` returns the path `p`; `as_path` of it returns `q`; the call
`fs::remove_dir` that the retry loop makes returns, with `Ok` or with an error whose kind is not
`Interrupted` (`CallReturns`); the `context` assumption for an `anyhow::Error`; and the
assumption about `format` and `from_str_nonconst` (`MessageSpecs`). -/
theorem remove_user_dir_if_empty_empty (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root Bool) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (his : is_empty_user self user = ok (.Ok true))
    (p : std.path.PathBuf) (hp : make_user_path_name self user = ok p) (q : std.path.Path)
    (hasp : pathBufAsPath p = ok q) (hr : CallReturns (removeDirCall q)) :
    remove_user_dir_if_empty self user = ok (.Ok ()) := by
  sorry

/-- conditional: if the user directory is not empty, `remove_user_dir_if_empty` returns `Ok ()`. In
the Rust source this path returns before the directory is removed. Hypotheses: `is_empty_user`
returns `Ok false`; the `context` assumption for an `anyhow::Error`; and the message
assumptions. -/
theorem remove_user_dir_if_empty_not_empty (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root Bool) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (his : is_empty_user self user = ok (.Ok false)) :
    remove_user_dir_if_empty self user = ok (.Ok ()) := by
  sorry

/-- conditional: if `is_empty_user` returns an error `e`, `remove_user_dir_if_empty` returns an
error with the same root cause. In the Rust source this path returns before the directory is
removed. Hypotheses: the outcome of `is_empty_user`; the `context` assumption for an
`anyhow::Error`; and the message assumptions. -/
theorem remove_user_dir_if_empty_err (root : anyhow.Error → ErrRoot) (hmsg : MessageSpecs)
    (hctx : AnyCtxLaw root Bool) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (e : anyhow.Error)
    (his : is_empty_user self user = ok (.Err e)) :
    ∃ e', remove_user_dir_if_empty self user = ok (.Err e') ∧ root e' = root e := by
  sorry

end Keystore2Verify.LegacyBlob
