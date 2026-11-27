import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
/-- conditional: if `make_user_path_name` returns the path `p0`, `make_super_key_filename` returns
`p0` with the component `.masterkey` pushed. Hypotheses: the outcome of `make_user_path_name`
(a translated function that reads the loader path), and the assumption about `push` of a `&str`
component. -/
theorem make_super_key_filename_ok (view : std.path.PathBuf → List Std.U8)
    (hpush : PathBufPushStrSpec view) (self : legacy_blob.LegacyBlobLoader)
    (user : utils.AndroidUserId) (p0 : std.path.PathBuf)
    (hp : make_user_path_name self user = ok p0) :
    ∃ p, make_super_key_filename self user = ok p ∧
      view p = pathPush (view p0) (utf8Bytes ".masterkey") := by
  sorry

end Keystore2Verify.LegacyBlob
