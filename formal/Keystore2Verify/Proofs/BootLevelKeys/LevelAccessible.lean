import Keystore2Verify.Specs.Defs.BootLevelKeys
import Keystore2Verify.Proofs.BootLevelKeys.BootLevel

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 keystore2.boot_level_keys Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.boot_level_keys.BootLevel.Insts
open CoreCloneClone renaming clone → bootLevelClone
open CoreCmpPartialEqBootLevel renaming eq → bootLevelEq
open CoreCmpOrd renaming cmp → bootLevelCmp
open CoreCmpPartialOrdBootLevel renaming partial_cmp → bootLevelPartialCmp
open keystore2.alloc.collections.vec_deque
open core.cmp.PartialOrd.ge renaming trait_default → geTraitDefault, «default» → geDefault
open core.cmp.PartialOrd renaming ge_body → geBody

/-- `L >= c` on boot levels never fails and compares the `usize` values. -/
theorem boot_level_ge (L c : BootLevel) :
    geTraitDefault CoreCmpPartialOrdBootLevel L c
      = ok (decide (L.val ≥ c.val)) := by
  have h := boot_level_partial_cmp L c
  simp only [geTraitDefault, geDefault,
    geBody]
  show (do let cmp ← bootLevelPartialCmp L c
           ok (decide (cmp = some Ordering.gt ∨ cmp = some Ordering.eq))) = _
  rw [h]
  rcases hc : compare L.val c.val with _ | _ | _
  all_goals simp_all [compare_gt_iff_gt, compare_lt_iff_lt]
  all_goals omega

/-- exact: a level below the current level is never accessible, whatever the queue holds. -/
theorem BootLevelKeyCache_level_accessible_lt (s : BootLevelKeyCache) (L : BootLevel)
    (h : L.val < s.current.val) : BootLevelKeyCache.level_accessible s L = ok false := by
  have hge : ¬ L.val ≥ s.current.val := by omega
  simp [BootLevelKeyCache.level_accessible, boot_level_ge, hge]

/-- conditional: `level_accessible` never fails, and it returns `true` exactly when the level is
at least the current level and the queue is not empty. This covers a level equal to the current
level, a level above it, an empty queue after `finish`, and a fresh cache (current level 0).
The hypothesis is the shared law for `VecDeque::is_empty`, for the view `view` of the queue. -/
theorem BootLevelKeyCache_level_accessible_iff (view : View)
    (hempty : ZVecQueueIsEmptyLaw view) (s : BootLevelKeyCache)
    (L : BootLevel) :
    ∃ b, BootLevelKeyCache.level_accessible s L = ok b ∧
      (b = true ↔ s.current.val ≤ L.val ∧ view s.cache ≠ []) := by
  obtain ⟨b, hb, hv⟩ := hempty s.cache
  by_cases hge : L.val ≥ s.current.val
  · refine ⟨!b, ?_, ?_⟩
    · simp [BootLevelKeyCache.level_accessible, boot_level_ge, hge, hb]
    · simp only [hge, true_and, Bool.not_eq_true']
      rw [ne_eq, ← hv]; simp
  · exact ⟨false, by simp [BootLevelKeyCache.level_accessible, boot_level_ge, hge], by simp; omega⟩

end Keystore2Verify.BootLevelKeys
