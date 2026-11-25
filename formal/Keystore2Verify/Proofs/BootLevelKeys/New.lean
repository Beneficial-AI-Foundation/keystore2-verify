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

/-- exact: if `new` returns a cache, its current level is 0. -/
theorem BootLevelKeyCache_new_current (k : keystore2_crypto.zvec.ZVec) (s : BootLevelKeyCache)
    (h : BootLevelKeyCache.new k = ok s) : s.current.val = 0 := by
  unfold BootLevelKeyCache.new at h
  cases h1 : VecDequeTGlobal.new keystore2_crypto.zvec.ZVec <;> simp [h1] at h
  rename_i c
  cases h2 : VecDeque.push_back c k <;> simp [h2] at h
  subst h
  rfl

/-- conditional: `new k` returns a cache at level 0 whose queue holds exactly the key `k`. The
hypotheses are the shared laws for `VecDeque::new` and `VecDeque::push_back`, for the view `view`
of the queue. -/
theorem BootLevelKeyCache_new_ok (view : View)
    (hnew : ZVecQueueNewLaw view)
    (hpush : ZVecQueuePushBackLaw view)
    (k : keystore2_crypto.zvec.ZVec) :
    ∃ s, BootLevelKeyCache.new k = ok s ∧ s.current.val = 0 ∧ view s.cache = [k] := by
  obtain ⟨q, hq, hv⟩ := hnew
  have hb : (view q).length < queueBound := by
    rw [hv]; simp [queueBound]; scalar_tac
  obtain ⟨q', hq', hv'⟩ := hpush q k hb
  refine ⟨{ current := 0#usize, cache := q' }, ?_, rfl, ?_⟩
  · simp [BootLevelKeyCache.new, hq, hq']
  · simpa [hv] using hv'

end Keystore2Verify.BootLevelKeys
