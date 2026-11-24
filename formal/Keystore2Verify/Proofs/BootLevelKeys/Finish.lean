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

/-- exact: if `finish` returns a cache, its current level is unchanged. -/
theorem BootLevelKeyCache_finish_current (s s' : BootLevelKeyCache)
    (h : BootLevelKeyCache.finish s = ok s') : s'.current = s.current := by
  sorry

/-- conditional: `finish` returns a cache with the same current level and an empty queue. The
hypothesis is the shared law for `VecDeque::clear`, for the view `view` of the queue. -/
theorem BootLevelKeyCache_finish_ok (view : View)
    (hclear : VecDequeClearLaw view VecDeque.clear) (s : BootLevelKeyCache) :
    ∃ s', BootLevelKeyCache.finish s = ok s' ∧ s'.current = s.current ∧ view s'.cache = [] := by
  sorry

end Keystore2Verify.BootLevelKeys
