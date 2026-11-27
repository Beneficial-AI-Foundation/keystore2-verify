import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
/-- conditional: if the alias has a known keystore prefix, `make_legacy_keystore_entry_filename`
returns `None`. In the Rust source this path logs a warning and returns before the path is
built. Hypotheses: the outcome of `is_keystore_alias` (an item the extraction could not
translate), and the assumptions about the logging calls. -/
theorem make_legacy_keystore_entry_filename_prefixed (hlog : LogSpecs)
    (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid) (al : Str)
    (his : is_keystore_alias al = ok true) :
    make_legacy_keystore_entry_filename self uid al = ok none := by
  sorry

/-- conditional: if the alias has no known keystore prefix, `make_legacy_keystore_entry_filename`
returns the path of the loader with two components pushed. In the Rust source they are
`user_` and the user number, then the uid, `_` and the encoded alias; the model does not observe
the text of `format!`, so the statement only says that two strings are pushed. Hypotheses: the
outcomes of `is_keystore_alias`, `owning_user` and `encode_alias`; the assumptions about `clone`
and `push` of a path buffer and about `format`. -/
theorem make_legacy_keystore_entry_filename_path (view : std.path.PathBuf → List Std.U8)
    (hclone : PathBufCloneSpec view) (hpush : PathBufPushStringSpec view)
    (hfmt : AllocFmtFormatSpec) (self : legacy_blob.LegacyBlobLoader) (uid : utils.AppUid)
    (al : Str) (user : utils.AndroidUserId) (enc : String)
    (his : is_keystore_alias al = ok false) (hu : utils.AppUid.owning_user uid = ok user)
    (hen : encode_alias al = ok enc) :
    ∃ p s1 s2, make_legacy_keystore_entry_filename self uid al = ok (some p) ∧
      view p = pathPush (pathPush (view self.path) (utf8Bytes s1)) (utf8Bytes s2) := by
  sorry

end Keystore2Verify.LegacyBlob
