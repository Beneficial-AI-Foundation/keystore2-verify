import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- conditional: `make_persistent_path` never returns an error. The result is `"file:"` followed
by the lossy string form `u` of `db_root` joined with `persistent.sqlite`. Hypotheses: the path
calls (see `persistentPathLossy`) return the view of a string `u`; the assumptions about
external functions `StrToOwnedSpec` and `StringPushStrSpec`. A path that is not valid UTF-8 is
changed by the lossy conversion before this point. -/
theorem make_persistent_path_ok (db_root : std.path.Path) (u : String)
    (h : u.toByteArray.size ≤ U32.max)
    (hto : StrToOwnedSpec) (hpush : StringPushStrSpec)
    (hpath : persistentPathLossy db_root = ok (toStr u h)) :
    database.KeystoreDB.make_persistent_path db_root = ok (.Ok ("file:" ++ u)) := by
  sorry
