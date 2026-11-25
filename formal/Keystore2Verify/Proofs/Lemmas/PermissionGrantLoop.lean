import Keystore2Verify.Specs.Defs.Permission
import Keystore2Verify.Proofs.Lemmas.BootLevelKeysBind
import Keystore2Verify.Proofs.Permission.IntoIter

/-!
# The permission loop of `check_grant_permission`

The loop takes the set bits of the access vector from the lowest up, and checks each as a
`KeyPerm` (a bit that is no `KeyPerm` is checked as `KeyPerm::None`). A check that returns an
error stops the loop with that error as root cause. In every iteration the message of the error
context is built with `format!`, also when the check succeeds.
-/

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open Keystore2Verify.Externals
open core.result.Result.Insts.CoreOpsTry renaming branch → tryBranch
open core.result.Result.Insts.CoreOpsTry_traitFromResidualResult
  renaming from_residual → fromResidual
open core.fmt.rt.Argument renaming new_debug → argNewDebug
open Aeneas.Std.core.fmt.Arguments renaming «new» → argumentsNew
open core.result.Result.Insts.AnyhowContext renaming context → resultContext
open anyhow.Error.Insts renaming AnyhowContextExtStdError → AnyhowExtStdError
open anyhow.context.ext.StdError renaming Blanket → StdBlanket
open keystore2_selinux.Error.Insts renaming CoreErrorError → SelinuxErrorError
open permission.KeyPermSet.Insts renaming CoreConvertFromKeyPerm → keyPermIntoSet
open permission.KeyPermSet.Insts.CoreIterTraitsCollectIntoIteratorKeyPermIntoIter
  renaming into_iter → setIntoIter
open permission.KeyPerm.Insts
open CoreConvertFromI32 renaming «from» → keyPermFromI32
open Keystore2Verify.BootLevelKeys

/-- Some set bit at the position `pos` or above gives a lowest such bit. -/
theorem exists_nextBit (s : permission.KeyPermSet) (pos : Nat)
    (h : ∃ j, pos ≤ j ∧ j < 32 ∧ HasBit s j) : ∃ i, NextBit s pos i := by
  classical
  have hex : ∃ j, pos ≤ j ∧ j < 32 ∧ HasBit s j := h
  refine ⟨Nat.find hex, ?_⟩
  obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
  exact ⟨h1, h2, h3, fun j hj hji hb =>
    Nat.find_min hex hji ⟨hj, by omega, hb⟩⟩

/-- A step of the loop at a set bit whose check returns `Ok` continues at the next position. -/
theorem grant_body_some_ok (hfmt : ∃ s, alloc.fmt.format (Unit.unit : core.fmt.Arguments) = ok s)
    (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c)
    (it : permission.perm.IntoIter) (i : Nat) (hi : NextBit it.vec it.pos.val i)
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (hchk : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
      = ok (.Ok ()))
    (root : anyhow.Error → ErrRoot) (hctxS : AnyhowStringCtxLaw root Unit) :
    ∃ it', permission.check_grant_permission_loop0.body caller_ctx target it
      = ok (.cont it') ∧ it'.vec = it.vec ∧ it'.pos.val = i + 1 := by
  obtain ⟨kp0, it', hk0, hn, hv, hp⟩ := into_iter_next_some it i hi
  rw [hk0] at hkp; simp only [Result.ok.injEq] at hkp; subst hkp
  have hc' : contextCStr target = ok c := hc
  refine ⟨it', ?_, hv, hp⟩
  unfold permission.check_grant_permission_loop0.body
  rw [hn]
  obtain ⟨s, hs⟩ := hfmt
  simp [hc', hchk, argNewDebug, argumentsNew, core.hint.must_use,
    hctxS.1, tryBranch]
  erw [Std.bind_ok, Std.bind_ok, hs]
  simp

/-- A step of the loop at a set bit whose check returns an error `e` finishes with an error that
has the root cause of `e`. -/
theorem grant_body_some_err (hfmt : ∃ s, alloc.fmt.format (Unit.unit : core.fmt.Arguments) = ok s)
    (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c)
    (it : permission.perm.IntoIter) (i : Nat) (hi : NextBit it.vec it.pos.val i)
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (e : anyhow.Error)
    (hchk : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
      = ok (.Err e))
    (root : anyhow.Error → ErrRoot) (hctxS : AnyhowStringCtxLaw root Unit) :
    ∃ e', permission.check_grant_permission_loop0.body caller_ctx target it
      = ok (.done (.Err e')) ∧ root e' = root e := by
  obtain ⟨kp0, it', hk0, hn, hv, hp⟩ := into_iter_next_some it i hi
  rw [hk0] at hkp; simp only [Result.ok.injEq] at hkp; subst hkp
  have hc' : contextCStr target = ok c := hc
  choose f hf1 hf2 using hctxS.2
  obtain ⟨s, hs⟩ := hfmt
  refine ⟨f e s, ?_, hf2 _ _⟩
  unfold permission.check_grant_permission_loop0.body
  rw [hn]
  simp [hc', hchk, argNewDebug, argumentsNew, core.hint.must_use,
    tryBranch,
    fromResidual]
  erw [Std.bind_ok, Std.bind_ok, hs]
  simp [hf1]

/-- A step of the loop at a set bit whose check fails with `x` fails with `x`. -/
theorem grant_body_some_fail
    (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c)
    (it : permission.perm.IntoIter) (i : Nat) (hi : NextBit it.vec it.pos.val i)
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp) (x : Error)
    (hchk : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
      = fail x) :
    permission.check_grant_permission_loop0.body caller_ctx target it = fail x := by
  obtain ⟨kp0, it', hk0, hn, hv, hp⟩ := into_iter_next_some it i hi
  rw [hk0] at hkp; simp only [Result.ok.injEq] at hkp; subst hkp
  have hc' : contextCStr target = ok c := hc
  unfold permission.check_grant_permission_loop0.body
  rw [hn]
  simp [hc', hchk]

/-- A step of the loop with no set bit at the position or above finishes with `Ok`. -/
theorem grant_body_none (caller_ctx : CStr) (target : keystore2_selinux.Context)
    (it : permission.perm.IntoIter) (hpos : it.pos.val ≤ 32)
    (hnone : ∀ j, it.pos.val ≤ j → j < 32 → ¬ HasBit it.vec j) :
    permission.check_grant_permission_loop0.body caller_ctx target it
      = ok (.done (.Ok ())) := by
  obtain ⟨it', hn, -, -⟩ := into_iter_next_none it hpos hnone
  unfold permission.check_grant_permission_loop0.body
  rw [hn]
  simp

/-- A loop step that continues leaves the loop at the new state. -/
theorem grant_loop_cont (caller_ctx : CStr) (target : keystore2_selinux.Context)
    (it it' : permission.perm.IntoIter)
    (h : permission.check_grant_permission_loop0.body caller_ctx target it = ok (.cont it')) :
    permission.check_grant_permission_loop0 it caller_ctx target =
      permission.check_grant_permission_loop0 it' caller_ctx target := by
  unfold permission.check_grant_permission_loop0
  rw [loop]
  simp [h]

/-- A loop step that finishes ends the loop with its result. -/
theorem grant_loop_done (caller_ctx : CStr) (target : keystore2_selinux.Context)
    (it : permission.perm.IntoIter) (r : core.result.Result Unit anyhow.Error)
    (h : permission.check_grant_permission_loop0.body caller_ctx target it = ok (.done r)) :
    permission.check_grant_permission_loop0 it caller_ctx target = ok r := by
  unfold permission.check_grant_permission_loop0
  rw [loop]
  simp [h]

/-- A loop step that fails makes the loop fail. -/
theorem grant_loop_fail (caller_ctx : CStr) (target : keystore2_selinux.Context)
    (it : permission.perm.IntoIter) (x : Error)
    (h : permission.check_grant_permission_loop0.body caller_ctx target it = fail x) :
    permission.check_grant_permission_loop0 it caller_ctx target = fail x := by
  unfold permission.check_grant_permission_loop0
  rw [loop]
  simp [h]

/-- If every set bit at the position or above passes its check, the loop returns `Ok`. -/
theorem grant_loop_ok (hfmt : AllocFmtFormatSpec) (root : anyhow.Error → ErrRoot)
    (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c) :
    ∀ (k : Nat) (it : permission.perm.IntoIter), 32 - it.pos.val = k → it.pos.val ≤ 32 →
      (∀ j, it.pos.val ≤ j → j < 32 → HasBit it.vec j →
        ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
          = ok (.Ok ())) →
      permission.check_grant_permission_loop0 it caller_ctx target = ok (.Ok ()) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro it hk hle hall
    by_cases hex : ∃ j, it.pos.val ≤ j ∧ j < 32 ∧ HasBit it.vec j
    · obtain ⟨i, hi⟩ := exists_nextBit _ _ hex
      obtain ⟨kp, hkp, hchk⟩ := hall i hi.1 hi.2.1 hi.2.2.1
      obtain ⟨it', hb, hv, hp⟩ := grant_body_some_ok (hfmt _) caller_ctx target c hc it i hi kp
        hkp hchk root hctxS
      rw [grant_loop_cont caller_ctx target it it' hb]
      have hi1 := hi.1
      have hi2 := hi.2.1
      have hlt : 32 - it'.pos.val < k := by omega
      exact ih (32 - it'.pos.val) hlt it' rfl (by omega)
        (fun j hj hj32 hb' => hall j (by omega) hj32 (hv ▸ hb'))
    · rw [grant_loop_done caller_ctx target it _
        (grant_body_none caller_ctx target it hle
          (fun j hj hj32 hb => hex ⟨j, hj, hj32, hb⟩))]

/-- The first failing set bit `i` ends the loop: if every set bit below `i` passes, and the
loop that starts at the position of the lowest set bit `i` satisfies `Q`, then so does the loop
from any earlier position at which no set bit below `i` is skipped. -/
theorem grant_loop_first (hfmt : AllocFmtFormatSpec) (root : anyhow.Error → ErrRoot)
    (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c)
    (Q : Result (core.result.Result Unit anyhow.Error) → Prop) (s : permission.KeyPermSet)
    (i : Nat) (hi : i < 32) (hset : HasBit s i)
    (hlow : ∀ j, j < i → HasBit s j → ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
          = ok (.Ok ()))
    (hlast : ∀ it : permission.perm.IntoIter, it.vec = s → NextBit it.vec it.pos.val i →
      Q (permission.check_grant_permission_loop0 it caller_ctx target)) :
    ∀ (k : Nat) (it : permission.perm.IntoIter), i - it.pos.val = k → it.pos.val ≤ i →
      it.vec = s → Q (permission.check_grant_permission_loop0 it caller_ctx target) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro it hk hle hvec
    obtain ⟨i', hi'⟩ := exists_nextBit it.vec it.pos.val ⟨i, hle, hi, hvec ▸ hset⟩
    have hi'le : i' ≤ i := by
      by_contra hlt
      exact hi'.2.2.2 i hle (by omega) (hvec ▸ hset)
    by_cases heq : i' = i
    · subst heq
      exact hlast it hvec hi'
    · have hlt : i' < i := by omega
      obtain ⟨kp, hkp, hchk⟩ := hlow i' hlt (hvec ▸ hi'.2.2.1)
      obtain ⟨it', hb, hv, hp⟩ := grant_body_some_ok (hfmt _) caller_ctx target c hc it i'
        hi' kp hkp hchk root hctxS
      rw [grant_loop_cont caller_ctx target it it' hb]
      have h1 := hi'.1
      exact ih (i - it'.pos.val) (by omega) it' rfl (by omega) (hv.trans hvec)

/-- A step of the loop at a set bit that returns a value has built its message: `format`
returned a string. -/
theorem grant_body_fmt (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c)
    (it : permission.perm.IntoIter) (i : Nat) (hi : NextBit it.vec it.pos.val i)
    (kp : permission.KeyPerm) (r : core.result.Result Unit anyhow.Error)
    (hchk : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
      = ok r)
    (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (b : ControlFlow permission.perm.IntoIter (core.result.Result Unit anyhow.Error))
    (hb : permission.check_grant_permission_loop0.body caller_ctx target it = ok b) :
    ∃ s, alloc.fmt.format (Unit.unit : core.fmt.Arguments) = ok s := by
  obtain ⟨kp0, it', hk0, hn, hv, hp⟩ := into_iter_next_some it i hi
  rw [hk0] at hkp; simp only [Result.ok.injEq] at hkp; subst hkp
  have hc' : contextCStr target = ok c := hc
  unfold permission.check_grant_permission_loop0.body at hb
  rw [hn] at hb
  simp [hc', hchk, argNewDebug, argumentsNew] at hb
  erw [Std.bind_ok, Std.bind_ok] at hb
  simp only [bind_eq_ok_iff] at hb
  obtain ⟨s, hs, -⟩ := hb
  exact ⟨s, hs⟩

/-- If the loop returns `Ok`, every set bit at the position or above passed its check. -/
theorem grant_loop_inv (root : anyhow.Error → ErrRoot)
    (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_ctx : CStr) (target : keystore2_selinux.Context) (c : CStr)
    (hc : contextCStr target = ok c) :
    ∀ (k : Nat) (it : permission.perm.IntoIter), 32 - it.pos.val = k → it.pos.val ≤ 32 →
      permission.check_grant_permission_loop0 it caller_ctx target = ok (.Ok ()) →
      ∀ j, it.pos.val ≤ j → j < 32 → HasBit it.vec j →
        ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp
          = ok (.Ok ()) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro it hk hle hloop j hj hj32 hjb
    obtain ⟨i, hi⟩ := exists_nextBit it.vec it.pos.val ⟨j, hj, hj32, hjb⟩
    obtain ⟨kp, it', hkp, hn, hv, hp⟩ := into_iter_next_some it i hi
    have hc' : contextCStr target = ok c := hc
    -- the loop at `it` ran a step, whose check returned some `r`
    obtain ⟨b, hb⟩ : ∃ b, permission.check_grant_permission_loop0.body caller_ctx target it
        = ok b := by
      unfold permission.check_grant_permission_loop0 at hloop
      rw [loop] at hloop
      simp only [bind_eq_ok_iff] at hloop
      obtain ⟨b, hb, -⟩ := hloop
      exact ⟨b, hb⟩
    obtain ⟨r, hr⟩ : ∃ r, keystore2_selinux.check_permission Keystore2_selinuxClassPermission
        caller_ctx c kp = ok r := by
      cases hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission
          caller_ctx c kp with
      | ret r => exact ⟨r, rfl⟩
      | vis i' k' =>
        exfalso
        unfold permission.check_grant_permission_loop0.body at hb
        rw [hn] at hb
        simp [hc', hcheck] at hb
      | div =>
        exfalso
        unfold permission.check_grant_permission_loop0.body at hb
        rw [hn] at hb
        simp [hc', hcheck] at hb
    have hfmt := grant_body_fmt caller_ctx target c hc it i hi kp r hr hkp b hb
    cases r with
    | Err e =>
      obtain ⟨e', hb', -⟩ := grant_body_some_err hfmt caller_ctx target c hc it i hi kp hkp e hr
        root hctxS
      rw [grant_loop_done caller_ctx target it _ hb'] at hloop
      simp at hloop
    | Ok u =>
      cases u
      obtain ⟨it', hb', hv', hp'⟩ := grant_body_some_ok hfmt caller_ctx target c hc it i hi kp
        hkp hr root hctxS
      rw [grant_loop_cont caller_ctx target it it' hb'] at hloop
      by_cases hji : j = i
      · subst hji; exact ⟨kp, hkp, hr⟩
      · have hlt : i < j := by
          have := hi.2.2.2 j hj
          by_contra hn'
          exact this (by omega) hjb
        have h1 := hi.1
        have h2 := hi.2.1
        exact ih (32 - it'.pos.val) (by omega) it' rfl (by omega) hloop j (by omega) hj32
          (hv' ▸ hjb)

end Keystore2Verify.Permission
