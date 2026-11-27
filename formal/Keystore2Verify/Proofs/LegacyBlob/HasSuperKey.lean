import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.LegacyBlobLoader
open std.path.Path renaming is_file → pathIsFile

/-- conditional: if `make_super_key_filename` returns the path `pb`, `deref` returns the path
view `p` and `is_file p` returns `b`, `has_super_key` returns `b`. A missing file gives `false`;
there is no error case. Hypotheses: the outcomes of the three calls. -/
theorem has_super_key_ok (self : legacy_blob.LegacyBlobLoader) (user : utils.AndroidUserId)
    (pb : std.path.PathBuf) (p : std.path.Path) (b : Bool)
    (hmk : make_super_key_filename self user = ok pb)
    (hd : pathBufDeref pb = ok p)
    (hf : pathIsFile p = ok b) :
    has_super_key self user = ok b := by
  sorry

end Keystore2Verify.LegacyBlob
