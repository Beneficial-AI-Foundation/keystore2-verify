import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open database.perboot.PerbootDB renaming insert_auth_token_entry → insertAuthTokenEntry
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone renaming clone → hatClone

/-- conditional: the function returns the same database `self`: the token is stored behind the
shared per-boot state, which `self` still points to. Hypotheses: `deref` of the shared state
returns `pd`; the clone of the token returns `hat`; the boot time `now` returns `bt`;
`AuthTokenEntry::new` returns `ate`; `insert_auth_token_entry` returns (the write lock is not
poisoned). The model has no link between the write and a later read, so no statement can say that
the token is in the set. -/
theorem insert_auth_token_ok (self : database.KeystoreDB)
    (auth_token : HardwareAuthToken.HardwareAuthToken)
    (pd : database.perboot.PerbootDB) (hat : HardwareAuthToken.HardwareAuthToken)
    (bt : database.BootTime) (ate : database.AuthTokenEntry)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hclone : hatClone auth_token = ok hat)
    (hnow : database.BootTime.now = ok bt)
    (hnew : database.AuthTokenEntry.new hat bt = ok ate)
    (hins : insertAuthTokenEntry pd ate = ok ()) :
    database.KeystoreDB.insert_auth_token self auth_token = ok self := by
  sorry

/-- conditional: if `insert_auth_token_entry` fails with `err`, the function fails with the same
`err`. This is propagation of any failure of that helper; in the Rust source it includes the panic
on a poisoned write lock. Hypotheses as in `insert_auth_token_ok`, except that
`insert_auth_token_entry` returns `fail err`. -/
theorem insert_auth_token_failure (self : database.KeystoreDB)
    (auth_token : HardwareAuthToken.HardwareAuthToken)
    (pd : database.perboot.PerbootDB) (hat : HardwareAuthToken.HardwareAuthToken)
    (bt : database.BootTime) (ate : database.AuthTokenEntry) (err : Error)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hclone : hatClone auth_token = ok hat)
    (hnow : database.BootTime.now = ok bt)
    (hnew : database.AuthTokenEntry.new hat bt = ok ate)
    (hins : insertAuthTokenEntry pd ate = fail err) :
    database.KeystoreDB.insert_auth_token self auth_token = fail err := by
  sorry
