import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.sync.poison
open std.sync.poison.mutex
open MutexGuard.Insts
open CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut

/-! In the Rust source `set_device_locked` removes the user from the set of unlocked users or
inserts it. The translation discards the new set that `remove` and `insert` return, and the write
back of `deref_mut`, so no statement can say that the set changed (blocked by extraction). The
statements below say when the function returns and when it panics. -/

/-- conditional: if locking the set of unlocked users returns a poison error, `set_device_locked`
panics (`fail`), for both values of the status. In the Rust source this path panics before the
set is changed. Hypothesis: the outcome of `Mutex::lock` on `self.device_unlocked_set`. -/
theorem set_device_locked_poisoned (self : enforcements.Enforcements)
    (user : utils.AndroidUserId) (status : Bool)
    (pe : PoisonError (MutexGuard UserSet))
    (hlock : Mutex.lock self.device_unlocked_set = ok (.Err pe)) :
    enforcements.Enforcements.set_device_locked self user status = fail Error.panic := by
  sorry

/-- conditional: if the status is "locked", the function removes the user from the set (in the Rust
source) and returns `()`. Hypotheses: the outcomes of `Mutex::lock` (the guard `g`), of `deref_mut`
on `g` (the set `hs`) and of `remove` on `hs` and `user` (it returns `r`). -/
theorem set_device_locked_locked (self : enforcements.Enforcements) (user : utils.AndroidUserId)
    (g : MutexGuard UserSet) (f : UserSet → MutexGuard UserSet) (hs : UserSet)
    (r : Bool × UserSet)
    (hlock : Mutex.lock self.device_unlocked_set = ok (.Ok g))
    (hmut : guardDerefMut g = ok (hs, f)) (hrem : userSetRemove hs user = ok r) :
    enforcements.Enforcements.set_device_locked self user true = ok () := by
  sorry

/-- conditional: if the status is "unlocked", the function inserts the user into the set (in the
Rust source) and returns `()`. Hypotheses: the outcomes of `Mutex::lock` (the guard `g`), of
`deref_mut` on `g` (the set `hs`) and of `insert` on `hs` and `user` (it returns `r`). -/
theorem set_device_locked_unlocked (self : enforcements.Enforcements) (user : utils.AndroidUserId)
    (g : MutexGuard UserSet) (f : UserSet → MutexGuard UserSet) (hs : UserSet)
    (r : Bool × UserSet)
    (hlock : Mutex.lock self.device_unlocked_set = ok (.Ok g))
    (hmut : guardDerefMut g = ok (hs, f)) (hins : userSetInsert hs user = ok r) :
    enforcements.Enforcements.set_device_locked self user false = ok () := by
  sorry
