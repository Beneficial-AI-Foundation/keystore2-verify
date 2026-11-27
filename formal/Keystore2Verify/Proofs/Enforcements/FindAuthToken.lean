import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open core.ops.function
open std.thread.local
open enforcements.Enforcements.find_auth_token.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0RefCellKeystoreDBOptionAuthTokenEntry → findOnce

/-- conditional: forwarding result. `find_auth_token` returns what `LocalKey::with` returns for the
closure and the predicate `p` on the thread-local database key. The statement does not say that
`with` runs the closure, so the closure body (`RefCell::borrow`, `deref` and the search
`find_auth_token_entry`) is reached by no statement, and which entry the search picks is not
stated, because `LocalKey::with` is an external function with no assumption.
Hypotheses: the outcomes of `globals::DB` (it returns `lk`) and of `LocalKey::with` on `lk` and the
predicate `p` (it returns `r`). The result is then `Ok r`. -/
theorem find_auth_token_with {F : Type}
    (hfn : Fn F database.AuthTokenEntry Bool) (p : F)
    (lk : LocalKey (core.cell.RefCell database.KeystoreDB))
    (r : Option database.AuthTokenEntry)
    (hdb : globals.DB = ok lk)
    (hwith : LocalKey.with (findOnce hfn) lk p = ok r) :
    enforcements.Enforcements.find_auth_token hfn p = ok r := by
  sorry
