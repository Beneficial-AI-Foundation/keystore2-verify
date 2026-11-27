import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
/-- conditional: `make_user_path_name` never fails. It returns the path of the loader with one
component pushed. In the Rust source the component is `user_` and the user number; the model
does not observe the text of `format!`, so the statement only says that some string is pushed.
Hypotheses: `view` is the view of a path; the assumptions about `clone` and `push` of a path
buffer and about `format`. -/
theorem make_user_path_name_ok (view : std.path.PathBuf → List Std.U8)
    (hclone : PathBufCloneSpec view) (hpush : PathBufPushStringSpec view)
    (hfmt : AllocFmtFormatSpec) (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId) :
    ∃ p s, make_user_path_name self user = ok p ∧
      view p = pathPush (view self.path) (utf8Bytes s) := by
  sorry

end Keystore2Verify.LegacyBlob
