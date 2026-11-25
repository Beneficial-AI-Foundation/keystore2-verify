import Keystore2Verify.Specs.Defs.Permission
import Keystore2Verify.Proofs.Lemmas.PermissionGrantLoop
import Keystore2Verify.Proofs.Permission.Includes

/-!
# The part of `check_grant_permission` after the target context

For both domains `APP` and `SELINUX` the body is the same once the target context is known. The
definition `grantTail` is that common part.
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
open core.ops.control_flow
open permission.KeyPerm.Insts
open permission.KeyPermSet.Insts.CoreConvertFromKeyPerm renaming «from» → setFromKeyPerm
open CoreConvertFromI32 renaming «from» → keyPermFromI32
open Keystore2Verify.BootLevelKeys

/-- `KeyPermSet::from(KeyPerm::Grant)` is the number 8. -/
theorem set_from_grant : setFromKeyPerm permission.KeyPerm.Grant = ok 8#i32 := by
  simp [setFromKeyPerm, lift]; rfl

/-- A set includes the number 8 exactly when its bit 3 is set. -/
theorem includes_grant_iff (s : permission.KeyPermSet) : Includes s 8#i32 ↔ HasBit s 3 := by
  unfold Includes HasBit
  constructor
  · intro h
    have := congrArg (fun x : Std.I32 => x.bv.getLsbD 3) h
    simpa using this
  · intro h
    apply I32.bv_eq_imp_eq
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    by_cases hj3 : j = 3
    · subst hj3; simp [h]
    · simp
      intro h8
      have h3 : Nat.testBit (2 ^ 3) j = true := by
        have := (by simpa [BitVec.getLsbD_ofNat] using h8 : j < 32 ∧ Nat.testBit 8 j = true)
        exact this.2
      rw [Nat.testBit_two_pow] at h3
      simp at h3
      omega

/-- The part of `check_grant_permission` after the target context `val` is known. -/
noncomputable def grantTail (caller_ctx : CStr) (access_vec : permission.KeyPermSet)
    (val : keystore2_selinux.Context) : Result (core.result.Result Unit anyhow.Error) := do
  let c ← contextCStr val
  let r2 ← keystore2_selinux.check_permission
    Keystore2_selinuxClassPermission caller_ctx c
    permission.KeyPerm.Grant
  let r3 ← resultContext
    AnyhowExtStdError
    (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay) r2 (toStr
    "Grant permission is required when granting.")
  let cf1 ← tryBranch r3
  match cf1 with
  | ControlFlow.Continue _ =>
    let b ← permission.KeyPermSet.includes (core.convert.IntoFrom
      keyPermIntoSet) access_vec
      permission.KeyPerm.Grant
    if b
    then
      let e ← keystore2_selinux.Error.perm
      resultContext
        (StdBlanket
        SelinuxErrorError)
        (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay)
        (.Err e) (toStr
        "Grant permission cannot be granted.")
    else
      let iter ←
        setIntoIter
          access_vec
      permission.check_grant_permission_loop0 iter caller_ctx val
  | ControlFlow.Break residual =>
    fromResidual
      Unit (core.convert.FromSame anyhow.Error) residual

theorem grant_eq_tail (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (ctx : keystore2_selinux.Context)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key =
      grantTail caller_ctx access_vec ctx := by
  rcases htarget with ⟨hd, hu, hg⟩ | ⟨hd, hl⟩
  · have hd' : key.domain = 0#iscalar := hd
    unfold permission.check_grant_permission
    simp [hd', hu, hg, hctxC.1, tryBranch, grantTail]
    rfl
  · have hd' : key.domain = 2#iscalar := hd
    unfold permission.check_grant_permission
    simp [hd', hl, hctxC.1, tryBranch, grantTail]
    rfl
/-- `includes` of `KeyPerm::Grant` never fails; it is `true` exactly when bit 3 is set. -/
theorem grant_includes (s : permission.KeyPermSet) :
    ∃ b, permission.KeyPermSet.includes
        (core.convert.IntoFrom keyPermIntoSet) s
        permission.KeyPerm.Grant = ok b ∧ (b = true ↔ HasBit s 3) := by
  obtain ⟨o, b, ho, hb, hiff⟩ := includes_key_perm s permission.KeyPerm.Grant
  rw [set_from_grant] at ho
  simp only [Result.ok.injEq] at ho
  subst ho
  exact ⟨b, hb, hiff.trans (includes_grant_iff s)⟩

/-- A failing view of the target context ends `grantTail` with that failure. -/
theorem grant_tail_deref_fail (caller_ctx : CStr) (av : permission.KeyPermSet)
    (ctx : keystore2_selinux.Context) (x : Error) (hc : contextCStr ctx = fail x) :
    grantTail caller_ctx av ctx = fail x := by
  have hc' : contextCStr ctx = fail x := hc
  unfold grantTail
  simp [hc']

/-- A failing check of `Grant` ends `grantTail` with that failure. -/
theorem grant_tail_check_fail (caller_ctx : CStr) (av : permission.KeyPermSet)
    (ctx : keystore2_selinux.Context) (c : CStr) (hc : contextCStr ctx = ok c) (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = fail x) :
    grantTail caller_ctx av ctx = fail x := by
  have hc' : contextCStr ctx = ok c := hc
  unfold grantTail
  simp [hc', hcheck]

/-- A check of `Grant` that returns an error `e` ends `grantTail` with an error of the same root
cause. -/
theorem grant_tail_check_err (root : anyhow.Error → ErrRoot)
    (hctxU : AnyhowStrCtxLaw root Unit) (caller_ctx : CStr) (av : permission.KeyPermSet)
    (ctx : keystore2_selinux.Context) (c : CStr) (hc : contextCStr ctx = ok c) (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Err e)) :
    ∃ e', grantTail caller_ctx av ctx = ok (.Err e') ∧ root e' = root e := by
  have hc' : contextCStr ctx = ok c := hc
  choose f hf1 hf2 using hctxU.2
  unfold grantTail
  simp [hc', hcheck, hf1, tryBranch,
    fromResidual]
  exact hf2 _ _

/-- If `Grant` passes and bit 3 of the access vector is set, `grantTail` returns the error
`PermissionDenied`. -/
theorem grant_tail_in_set (root : anyhow.Error → ErrRoot)
    (hctxU : AnyhowStrCtxLaw root Unit) (hsel : SelinuxStrCtxLaw root)
    (caller_ctx : CStr) (av : permission.KeyPermSet)
    (ctx : keystore2_selinux.Context) (c : CStr) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : HasBit av 3) :
    ∃ e, grantTail caller_ctx av ctx = ok (.Err e) ∧ root e = deniedRoot := by
  have hc' : contextCStr ctx = ok c := hc
  obtain ⟨b, hb, hiff⟩ := grant_includes av
  have hbt : b = true := hiff.2 hbit
  choose f hf1 hf2 using hsel.2
  unfold grantTail
  simp [hc', hcheck, hctxU.1, hb, hbt, hf1, tryBranch,
    keystore2_selinux.Error.perm]
  exact (hf2 _ _).trans rfl

/-- If `Grant` passes and bit 3 of the access vector is clear, `grantTail` runs the loop over the
permissions of the access vector. -/
theorem grant_tail_loop (root : anyhow.Error → ErrRoot)
    (hctxU : AnyhowStrCtxLaw root Unit)
    (caller_ctx : CStr) (av : permission.KeyPermSet)
    (ctx : keystore2_selinux.Context) (c : CStr) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit av 3) :
    grantTail caller_ctx av ctx =
      permission.check_grant_permission_loop0 { vec := av, pos := 0#u8 } caller_ctx ctx := by
  have hc' : contextCStr ctx = ok c := hc
  obtain ⟨b, hb, hiff⟩ := grant_includes av
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd (hiff.1 rfl) hbit
  unfold grantTail
  simp [hc', hcheck, hctxU.1, hb, hbf, tryBranch,
    key_perm_set_into_iter]

/-- If `grantTail` returns `Ok`, bit 3 is clear, `Grant` passed, and every set bit passed. -/
theorem grant_tail_inv (root : anyhow.Error → ErrRoot)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (hsel : SelinuxStrCtxLaw root)
    (caller_ctx : CStr) (av : permission.KeyPermSet) (ctx : keystore2_selinux.Context)
    (h : grantTail caller_ctx av ctx = ok (.Ok ())) :
    ¬ HasBit av 3 ∧ ∃ c, contextCStr ctx = ok c ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
        permission.KeyPerm.Grant = ok (.Ok ()) ∧
      ∀ i, i < 32 → HasBit av i → ∃ kp, keyPermFromI32 (bitVal i) = ok kp ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
          ok (.Ok ()) := by
  choose fU hfU1 hfU2 using hctxU.2
  choose fS hfS1 hfS2 using hsel.2
  unfold grantTail at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨c, hc, r2, hr2, r3, hr3, cf1, hcf1, h⟩ := h
  have hc' : contextCStr ctx = ok c := hc
  cases r2 with
  | Err e =>
    rw [hfU1] at hr3
    simp only [Result.ok.injEq] at hr3; subst hr3
    simp [tryBranch] at hcf1; subst hcf1
    simp [fromResidual] at h
  | Ok u =>
    cases u
    rw [hctxU.1] at hr3
    simp only [Result.ok.injEq] at hr3; subst hr3
    simp [tryBranch] at hcf1; subst hcf1
    obtain ⟨b, hb, hiff⟩ := grant_includes av
    rw [hb] at h
    by_cases hbt : b = true
    · exfalso
      simp [hbt, keystore2_selinux.Error.perm, hfS1] at h
    · have hbit : ¬ HasBit av 3 := fun hh => hbt (hiff.2 hh)
      have hbf : b = false := by simpa using hbt
      simp [hbf, key_perm_set_into_iter] at h
      refine ⟨hbit, c, hc', hr2, ?_⟩
      intro i hi hb
      exact grant_loop_inv root hctxS caller_ctx ctx c hc' _ { vec := av, pos := 0#u8 } rfl
        (by simp) h i (by simp) hi hb

/-- If the function returns `Ok`, the target context came from `getcon` (domain `APP`, uid equal
to the namespace) or from the lookup (domain `SELINUX`). -/
theorem grant_front_inv (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hsel : SelinuxStrCtxLaw root) (hks : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (av : permission.KeyPermSet) (key : KeyDesc)
    (h : permission.check_grant_permission caller_uid caller_ctx av key = ok (.Ok ())) :
    ∃ ctx, ((key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))) := by
  choose fC hfC1 hfC2 using hctxC.2
  choose fS hfS1 hfS2 using hsel.2
  choose fK hfK1 hfK2 using hks.2
  unfold permission.check_grant_permission at h
  dsimp only at h
  split at h
  · rename_i hd
    have hd' : key.domain = domainApp := hd
    by_cases hu : caller_uid = key.nspace
    · simp only [hu, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, hr, r1, hr1, cf, hcf, h⟩ := h
      cases r with
      | Ok ctx => exact ⟨ctx, Or.inl ⟨hd', hu, hr⟩⟩
      | Err e =>
        rw [hfC1] at hr1
        simp only [Result.ok.injEq] at hr1; subst hr1
        simp [tryBranch] at hcf; subst hcf
        simp [fromResidual] at h
    · exfalso
      have hu' : (caller_uid != key.nspace) = true := by simpa using hu
      simp only [hu', ite_true] at h
      simp [keystore2_selinux.Error.perm, hfS1] at h
  · rename_i hd
    have hd' : key.domain = domainSelinux := hd
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hr, r1, hr1, cf, hcf, h⟩ := h
    cases r with
    | Ok ctx => exact ⟨ctx, Or.inr ⟨hd', hr⟩⟩
    | Err e =>
      rw [hfC1] at hr1
      simp only [Result.ok.injEq] at hr1; subst hr1
      simp [tryBranch] at hcf; subst hcf
      simp [fromResidual] at h
  · exfalso
    simp [error.Error.sys, argNewDebug, argumentsNew,
      core.hint.must_use] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨_, -, _, -, s, -, h⟩ := h
    rw [hfK1] at h
    simp at h

end Keystore2Verify.Permission
