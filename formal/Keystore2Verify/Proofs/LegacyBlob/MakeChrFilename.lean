import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
/-- conditional: if `owning_user` returns `user`, `make_user_path_name` returns `p0`, and the
formatted string `s1` (the text that Rust encodes) has the `&str` view `s2` for which
`encode_alias` returns `enc`, `make_chr_filename` returns `p0` with one component pushed. In the
Rust source the component is `.`, the uid, `_chr_` and the encoded alias; the model does not
observe the text of `format!`, so the statement only says that some string is pushed.
Hypotheses: the outcomes of `owning_user`, of the first `format` (which builds the text to
encode), of `String::deref` on it, of `encode_alias` (an item the extraction could not
translate) on that `&str`, and of `make_user_path_name`; the assumptions about `push` of a
`String` component and about `format` (for the second `format`). -/
theorem make_chr_filename_ok (view : std.path.PathBuf → List Std.U8)
    (hpush : PathBufPushStringSpec view) (hfmt : AllocFmtFormatSpec)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al pre : Str)
    (user : utils.AndroidUserId) (s1 : String) (s2 : Str) (enc : String) (p0 : std.path.PathBuf)
    (hu : utils.AppUid.owning_user uid = ok user)
    (hf : alloc.fmt.format () = ok s1) (hd : stringAsStr s1 = ok s2)
    (henc : encode_alias s2 = ok enc) (hp : make_user_path_name self user = ok p0) :
    ∃ p s, make_chr_filename self uid al pre = ok p ∧
      view p = pathPush (view p0) (utf8Bytes s) := by
  sorry

end Keystore2Verify.LegacyBlob
