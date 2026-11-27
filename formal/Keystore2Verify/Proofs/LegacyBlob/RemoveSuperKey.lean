import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.LegacyBlobLoader
open std.path.PathBuf renaming as_path → pathBufAsPath

/-- conditional: if the user directory is empty after the attempt to remove the super key file
returns, the Rust source also attempts to remove the directory; `remove_super_key` returns `()`
whenever both attempts return a Rust result, including an error. Hypotheses:
`make_super_key_filename` returns `p1` and `as_path` of it `q1`; the call `fs::remove_file` that
the retry loop makes returns (`CallReturns`); `is_empty_user` returns `Ok true`;
`make_user_path_name` returns `p2` and `as_path` of it `q2`; the call `fs::remove_dir` returns
(`CallReturns`). -/
theorem remove_super_key_empty (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (p1 p2 : std.path.PathBuf) (q1 q2 : std.path.Path)
    (hmk : make_super_key_filename self user = ok p1) (hasp1 : pathBufAsPath p1 = ok q1)
    (hr1 : CallReturns (removeFileCall q1))
    (his : is_empty_user self user = ok (.Ok true))
    (hup : make_user_path_name self user = ok p2) (hasp2 : pathBufAsPath p2 = ok q2)
    (hr2 : CallReturns (removeDirCall q2)) :
    remove_super_key self user = ok () := by
  sorry

/-- conditional: if the user directory is not empty after the attempt to remove the super key file
returns, `remove_super_key` returns `()`. In the Rust source this path does not remove the
directory. Hypotheses: `make_super_key_filename` returns `p1` and `as_path` of it `q1`; the call
`fs::remove_file` that the retry loop makes returns (`CallReturns`); `is_empty_user` returns `Ok
false`. -/
theorem remove_super_key_not_empty (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (p1 : std.path.PathBuf) (q1 : std.path.Path)
    (hmk : make_super_key_filename self user = ok p1) (hasp1 : pathBufAsPath p1 = ok q1)
    (hr1 : CallReturns (removeFileCall q1))
    (his : is_empty_user self user = ok (.Ok false)) :
    remove_super_key self user = ok () := by
  sorry

/-- conditional: if `is_empty_user` returns an error, `remove_super_key` treats it as "not empty"
and returns `()`. In the Rust source this path does not remove the directory. Hypotheses: as for
`remove_super_key_not_empty`, with `is_empty_user` returning `Err e`. -/
theorem remove_super_key_empty_err (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (p1 : std.path.PathBuf) (q1 : std.path.Path) (e : anyhow.Error)
    (hmk : make_super_key_filename self user = ok p1) (hasp1 : pathBufAsPath p1 = ok q1)
    (hr1 : CallReturns (removeFileCall q1))
    (his : is_empty_user self user = ok (.Err e)) :
    remove_super_key self user = ok () := by
  sorry

end Keystore2Verify.LegacyBlob
