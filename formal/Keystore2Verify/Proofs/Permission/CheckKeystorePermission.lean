import Keystore2Verify.Specs.Defs.Permission
import Keystore2Verify.Proofs.Lemmas.BootLevelKeysBind

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
open permission.KeystorePerm.Insts
open Keystore2Verify.BootLevelKeys

/-! `check_keystore_permission` calls `getcon`, adds a message to its error, and then checks the
permission of the caller against that context. The theorems below name the outcome of each call.
`contextCStr ctx = ok c` says that the context `ctx` has the view `c` as a `CStr`. -/

/-- conditional: if `getcon` returns the context `ctx`, and the check of `perm` against it returns
`Ok`, then the function returns `Ok`. Hypotheses: the `context` law for an `anyhow::Error` result
with a `&str` message (`AnyhowStrCtxLaw`, it keeps an `Ok`), and the outcomes of `getcon`, of the
view of `ctx` as a `CStr`, and of `check_permission` for the class `keystore2` and `perm`. -/
theorem check_keystore_permission_ok (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_keystore_permission caller_ctx perm = ok (.Ok ()) := by
  have hc' : contextCStr ctx = ok c := hc
  unfold permission.check_keystore_permission
  simp [hget, hctx.1, tryBranch, hc', hcheck]

/-- conditional: if `getcon` returns an error `e`, the function returns an error with the same
root cause as `e`. In the Rust source this path returns before `check_permission` is called.
Hypotheses: the `context` law of
`check_keystore_permission_ok`, and the outcome of `getcon`. -/
theorem check_keystore_permission_getcon_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_keystore_permission caller_ctx perm = ok (.Err e') ∧
      root e' = root e := by
  choose f hf1 hf2 using hctx.2
  unfold permission.check_keystore_permission
  simp [hget, hf1, tryBranch,
    fromResidual]
  exact hf2 _ _

/-- conditional: if `getcon` returns the context `ctx` and the check of `perm` returns an error
`e`, the function returns the same error `e`. Hypotheses: the `context` law of
`check_keystore_permission_ok` (the `context` call of `getcon` keeps the `Ok`), and the outcomes
of `getcon`, of the view of `ctx`, and of `check_permission`. -/
theorem check_keystore_permission_check_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr) (e : anyhow.Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    permission.check_keystore_permission caller_ctx perm = ok (.Err e) := by
  have hc' : contextCStr ctx = ok c := hc
  unfold permission.check_keystore_permission
  simp [hget, hctx.1, tryBranch, hc', hcheck]

/-- conditional: if `getcon` fails with `x`, the function returns the same `fail x`. In the Rust
source this path returns before `check_permission` is called. Hypothesis: the outcome of `getcon`.
No law is needed. -/
theorem check_keystore_permission_getcon_fail (caller_ctx : CStr)
    (perm : permission.KeystorePerm) (x : Error)
    (hget : keystore2_selinux.getcon = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x := by
  unfold permission.check_keystore_permission
  simp [hget]

/-- conditional: if `getcon` returns the context `ctx` and the check of `perm` fails with `x`, the
function returns the same `fail x`. Hypotheses: the `context` law of
`check_keystore_permission_ok`, and the outcomes of `getcon`, of the view of `ctx`, and of
`check_permission`. -/
theorem check_keystore_permission_check_fail (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr) (x : Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x := by
  have hc' : contextCStr ctx = ok c := hc
  unfold permission.check_keystore_permission
  simp [hget, hctx.1, tryBranch, hc', hcheck]

/-- conditional: if `getcon` returns the context `ctx` and the view of `ctx` as a `CStr` fails with
`x`, the function returns the same `fail x`. Hypotheses: the `context` law of
`check_keystore_permission_ok`, and the outcomes of `getcon` and of the view. -/
theorem check_keystore_permission_deref_fail (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (x : Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x := by
  have hc' : contextCStr ctx = fail x := hc
  unfold permission.check_keystore_permission
  simp [hget, hctx.1, tryBranch, hc']


/-- Successful authorization used the returned context and a successful check of this permission. -/
theorem check_keystore_permission_ok_of_result (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (h : permission.check_keystore_permission caller_ctx perm = ok (.Ok ())) :
    ∃ ctx c, keystore2_selinux.getcon = ok (.Ok ctx) ∧ contextCStr ctx = ok c ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c perm =
        ok (.Ok ()) := by
  choose f hf1 hf2 using hctx.2
  unfold permission.check_keystore_permission at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, r1, hr1, cf, hcf, h⟩ := h
  cases r with
  | Ok ctx =>
    rw [hctx.1] at hr1
    simp only [Result.ok.injEq] at hr1; subst hr1
    simp [tryBranch] at hcf
    subst hcf
    simp only [bind_eq_ok_iff] at h
    obtain ⟨c, hc, h⟩ := h
    exact ⟨ctx, c, hr, hc, h⟩
  | Err e =>
    rw [hf1] at hr1
    simp only [Result.ok.injEq] at hr1; subst hr1
    simp [tryBranch] at hcf
    subst hcf
    simp [fromResidual] at h

end Keystore2Verify.Permission
