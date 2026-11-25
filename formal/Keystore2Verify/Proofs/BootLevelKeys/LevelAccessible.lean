import Keystore2Verify.Specs.Defs.BootLevelKeys

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp
open keystore2.alloc.collections.vec_deque

/-- exact: a level below the current level is never accessible, whatever the queue holds. -/
theorem BootLevelKeyCache_level_accessible_lt (s : BootLevelKeyCache) (L : BootLevel)
    (h : L.val < s.current.val) : BootLevelKeyCache.level_accessible s L = ok false := by
  sorry

/-- conditional: `level_accessible` never fails, and it returns `true` exactly when the level is
at least the current level and the queue is not empty. This covers a level equal to the current
level, a level above it, an empty queue after `finish`, and a fresh cache (current level 0).
The hypothesis is the shared law for `VecDeque::is_empty`, for the view `view` of the queue. -/
theorem BootLevelKeyCache_level_accessible_iff (view : View)
    (hempty : ZVecQueueIsEmptyLaw view) (s : BootLevelKeyCache)
    (L : BootLevel) :
    ∃ b, BootLevelKeyCache.level_accessible s L = ok b ∧
      (b = true ↔ s.current.val ≤ L.val ∧ view s.cache ≠ []) := by
  sorry

end Keystore2Verify.BootLevelKeys
