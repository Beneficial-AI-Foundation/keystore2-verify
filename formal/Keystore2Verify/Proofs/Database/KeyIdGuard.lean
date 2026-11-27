import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open std.sync.poison
open database.KeyIdGuard renaming id → keyIdGuardId
open database.KeyIdLockDb renaming try_get → keyIdLockDbTryGet

/-- exact: `id` never fails and returns the locked key id. -/
theorem key_id_guard_id (g : database.KeyIdGuard) : keyIdGuardId g = ok g := by
  sorry

/-- conditional: `try_get` returns `Some(KeyIdGuard(key_id))` when the key id was not in the set
of locked keys. Hypotheses: `lock` returned a guard `g` (the mutex is not poisoned); `deref_mut`
of `g` returned the set `hs`; `HashSet::insert` of `key_id` into `hs` returned `true` (the key
was not present). The translation returns only the option. Nothing is stated about the set of
locked keys after the call. -/
theorem key_id_lock_db_try_get_acquired (self : database.KeyIdLockDb) (key_id : Std.I64)
    (g : KeySetGuard) (hs hs' : KeySet) (back : KeySet → KeySetGuard)
    (hlock : keySetLock self.locked_keys = ok (.Ok g))
    (hderef : keySetDerefMut g = ok (hs, back))
    (hins : keySetInsert hs key_id = ok (true, hs')) :
    keyIdLockDbTryGet self key_id = ok (some key_id) := by
  sorry

/-- conditional: `try_get` returns `None` when the key id was already in the set of locked keys.
Hypotheses: as for `key_id_lock_db_try_get_acquired`, but `insert` returned `false`. The
translation returns only the option. Nothing is stated about the set of locked keys after the
call. -/
theorem key_id_lock_db_try_get_taken (self : database.KeyIdLockDb) (key_id : Std.I64)
    (g : KeySetGuard) (hs hs' : KeySet) (back : KeySet → KeySetGuard)
    (hlock : keySetLock self.locked_keys = ok (.Ok g))
    (hderef : keySetDerefMut g = ok (hs, back))
    (hins : keySetInsert hs key_id = ok (false, hs')) :
    keyIdLockDbTryGet self key_id = ok none := by
  sorry

/-- conditional: `try_get` panics when the mutex is poisoned (`lock` returned an error, and
`unwrap` panics on it). Hypothesis: `lock` returned the error `e`. -/
theorem key_id_lock_db_try_get_poisoned (self : database.KeyIdLockDb) (key_id : Std.I64)
    (e : PoisonError KeySetGuard)
    (hlock : keySetLock self.locked_keys = ok (.Err e)) :
    keyIdLockDbTryGet self key_id = fail .panic := by
  sorry
