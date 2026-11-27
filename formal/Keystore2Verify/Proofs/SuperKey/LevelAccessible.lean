import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open std.sync.poison
open std.sync.poison.mutex
open std.sync.poison.mutex.MutexGuard.Insts

/-- conditional: if the manager has no boot level cache, the function returns `false`. In the
Rust source this path returns before the lock is taken. Hypothesis: the assumption about
`Option::as_ref` at the mutex of the cache. -/
theorem SuperKeyManager_level_accessible_no_cache
    (hasref : OptionAsRefSpec (Mutex boot_level_keys.BootLevelKeyCache))
    (self : super_key.SuperKeyManager) (L : boot_level_keys.BootLevel)
    (h : self.data.boot_level_key_cache = none) :
    super_key.SuperKeyManager.level_accessible self L = ok false := by
  sorry

/-- conditional: if the manager has a cache in the mutex `m` and `m.lock()` returns the error
`PoisonError`, the function panics (`unwrap` on `Err`). Hypotheses: the assumption about
`Option::as_ref`, and the outcome of the lock. -/
theorem SuperKeyManager_level_accessible_poisoned
    (hasref : OptionAsRefSpec (Mutex boot_level_keys.BootLevelKeyCache))
    (self : super_key.SuperKeyManager) (L : boot_level_keys.BootLevel)
    (m : Mutex boot_level_keys.BootLevelKeyCache)
    (p : PoisonError
      (MutexGuard boot_level_keys.BootLevelKeyCache))
    (hc : self.data.boot_level_key_cache = some m)
    (hlock : Mutex.lock m = ok (.Err p)) :
    super_key.SuperKeyManager.level_accessible self L = fail Error.panic := by
  sorry

/-- conditional: if the manager has a cache in the mutex `m`, `m.lock()` returns the guard `g`,
and the guard gives the cache `c`, the function never fails and returns `true` exactly when `L`
is at least the current level of `c` and the queue of `c` is not empty. The queue is read through
`view`. The statement is about the cache `c` that the guard gives; the translation does not tie
`c` to the mutex, and does not show that the lock is released. Hypotheses: the assumption about
`Option::as_ref`, the assumption about `VecDeque::is_empty`, and the outcomes of the lock and of
the dereference of the guard. -/
theorem SuperKeyManager_level_accessible_iff
    (hasref : OptionAsRefSpec (Mutex boot_level_keys.BootLevelKeyCache))
    (view : ZVecQueue → List keystore2_crypto.zvec.ZVec) (hempty : ZVecQueueIsEmptyLaw view)
    (self : super_key.SuperKeyManager) (L : boot_level_keys.BootLevel)
    (m : Mutex boot_level_keys.BootLevelKeyCache)
    (g : MutexGuard boot_level_keys.BootLevelKeyCache)
    (c : boot_level_keys.BootLevelKeyCache)
    (hc : self.data.boot_level_key_cache = some m)
    (hlock : Mutex.lock m = ok (.Ok g))
    (hderef : CoreOpsDerefDeref.deref g = ok c) :
    ∃ b, super_key.SuperKeyManager.level_accessible self L = ok b ∧
      (b = true ↔ c.current.val ≤ L.val ∧ view c.cache ≠ []) := by
  sorry

end Keystore2Verify.SuperKey
