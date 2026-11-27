import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open database.perboot.PerbootDB renaming find_auth_token_entry → findAuthTokenEntry
open core.ops.function renaming Fn → FnTrait

/-- conditional: the result is the result of the search for an entry that satisfies `p` in the
shared per-boot state. In the Rust source this is the newest such entry, or none; the search is
not translated, so no statement can say which entry it finds. The database is not changed.
Hypothesis: `deref` of the shared state returns `pd`. -/
theorem find_auth_token_entry_search {F : Type _}
    (inst : FnTrait F database.AuthTokenEntry Bool)
    (self : database.KeystoreDB) (p : F) (pd : database.perboot.PerbootDB)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd) :
    database.KeystoreDB.find_auth_token_entry inst self p =
      findAuthTokenEntry inst pd p := by
  sorry
