import Keystore2Verify.Specs.Defs.Permission
import Keystore2Verify.Proofs.Lemmas.PermissionGrantTail

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

/-! `check_grant_permission` works in this order, and a failing step returns at once:

1. By the domain of the key, it computes the target context. `APP`: the caller uid must equal the
   namespace, and the target is the context of `getcon`. `SELINUX`: the target is the lookup of
   the namespace. Any other domain is an error.
2. The caller must hold the permission `Grant` for the target.
3. The set `access_vec` must not contain `Grant` (bit 3).
4. The caller must hold every permission of `access_vec`, checked from the lowest bit up. A bit that
   is no `KeyPerm` is checked as `KeyPerm::None`.

In the theorems, `contextCStr ctx = ok c` says that the context `ctx` has the view `c` as a
`CStr`. `htarget` says that step 1 succeeded: for `APP` the uid equals the namespace and `getcon`
returned `ctx`, for `SELINUX` the lookup returned `ctx`.
A hypothesis about a call of `check_permission` for the permission `p` is a hypothesis about that
call only. The translation models a repeated call with the same arguments as one pure function, so
two calls with the same arguments have the same outcome in every statement. The loop checks bits
that are no `KeyPerm` as `KeyPerm::None`, so two such bits make two identical calls. The success
statements cover these access vectors too: they cover the runs in which the repeated check gives the
same answer each time. A run in which the policy answer changes between the two calls is outside
the model.

In the generated loop, the message of `check_permission failed` is built (`alloc.fmt.format`)
before `context` is applied, in every iteration, also when the check returns `Ok`. So the
statements that run the loop at least once take the `format` law (`AllocFmtFormatSpec`).
Where a statement says that an outcome is `fail x`, the generated function returns `fail x` at once. -/

/-- conditional: the domain is `APP` and the caller uid differs from the namespace. The result is
an error whose root cause is `selinux::Error::PermissionDenied`. Hypothesis: the `context` law for
a SELinux error with a `&str` message (`SelinuxStrCtxLaw`). -/
theorem check_grant_permission_foreign_app (root : anyhow.Error → ErrRoot)
    (hctx : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainApp) (hne : caller_uid ≠ key.nspace) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = deniedRoot := by
  have hd' : key.domain = 0#iscalar := hdom
  choose f hf1 hf2 using hctx.2
  unfold permission.check_grant_permission
  simp [hd', hne, keystore2_selinux.Error.perm, hf1]
  exact (hf2 _ _).trans rfl

/-- conditional: the domain is `APP`, the caller uid equals the namespace, and `getcon` returns an
error `e`. The result is an error with the same root cause as `e`. Hypotheses: the `context` law
for an `anyhow::Error` result with a `&str` message and a context value (`AnyhowStrCtxLaw`), and
the outcome of `getcon`. -/
theorem check_grant_permission_app_getcon_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e := by
  have hd' : key.domain = 0#iscalar := hdom
  choose f hf1 hf2 using hctx.2
  unfold permission.check_grant_permission
  simp [hd', heq, hget, hf1, tryBranch,
    fromResidual]
  exact hf2 _ _

/-- conditional: the domain is `SELINUX` and the lookup of the namespace returns an error `e`. The
result is an error with the same root cause as `e`. The uid is not compared. Hypotheses: the same
`context` law as `check_grant_permission_app_getcon_err`, and the outcome of the lookup. -/
theorem check_grant_permission_selinux_lookup_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainSelinux)
    (e : anyhow.Error) (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e := by
  have hd' : key.domain = 2#iscalar := hdom
  choose f hf1 hf2 using hctx.2
  unfold permission.check_grant_permission
  simp [hd', hlook, hf1, tryBranch,
    fromResidual]
  exact hf2 _ _

/-- conditional: the domain is `APP`, the caller uid equals the namespace, and `getcon` fails with
`x`. The result is `fail x`. Hypothesis: the outcome of `getcon`. No law is
needed. -/
theorem check_grant_permission_app_getcon_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (x : Error) (hget : keystore2_selinux.getcon = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x := by
  have hd' : key.domain = 0#iscalar := hdom
  unfold permission.check_grant_permission
  simp [hd', heq, hget]

/-- conditional: the domain is `SELINUX` and the lookup of the namespace fails with `x`.
The result is `fail x`; this equation does not identify the cause of the opaque failure. Hypothesis: the
outcome of the lookup. No law is needed. -/
theorem check_grant_permission_selinux_lookup_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hdom : key.domain = domainSelinux)
    (x : Error) (hlook : permission.lookup_keystore2_key_context key.nspace = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x := by
  have hd' : key.domain = 2#iscalar := hdom
  unfold permission.check_grant_permission
  simp [hd', hlook]

/-- conditional: the domain is neither `APP` nor `SELINUX` (`GRANT`, `BLOB`, `KEY_ID` and every
other number). The result is an error whose root cause is the keystore2 error with the response
code `SYSTEM_ERROR`. In the Rust source this path returns before the uid is compared and before
`check_permission` is called. Hypotheses: the `format`
law (`AllocFmtFormatSpec`), and the `context` law for a keystore2 error with a `String` message
(`KsStringCtxLaw`). -/
theorem check_grant_permission_other_domain (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (happ : key.domain ≠ domainApp) (hsel : key.domain ≠ domainSelinux) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = .ks sysError := by
  have h0 : ¬ key.domain = 0#iscalar := happ
  have h2 : ¬ key.domain = 2#iscalar := hsel
  choose f hf1 hf2 using hctx.2
  obtain ⟨s, hs⟩ := hfmt (Unit.unit : core.fmt.Arguments)
  refine ⟨f sysError s, ?_, (hf2 _ _).trans rfl⟩
  unfold permission.check_grant_permission
  generalize key.domain = d at *
  dsimp only
  split
  · exact absurd rfl h0
  · exact absurd rfl h2
  · simp [error.Error.sys, sysError, argNewDebug, argumentsNew,
      core.hint.must_use]
    erw [Std.bind_ok, Std.bind_ok, hs]
    simp [hf1]

/-- conditional: the target is `c` and the check of `Grant` returns an error `e`. The result is an
error with the same root cause as `e`, whatever `access_vec` is. Hypotheses: the `context` laws
for a context value and for `()` with a `&str` message (`AnyhowStrCtxLaw`), and the outcomes that
`htarget` names and the outcome of `check_permission` for `Grant`. -/
theorem check_grant_permission_grant_check_err (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))) (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  exact grant_tail_check_err root hctxU caller_ctx access_vec ctx c hc e hcheck

/-- conditional: the target is `ctx` and the view of `ctx` as a `CStr` fails with `x`.
The result is `fail x`, whatever `access_vec` is. Hypotheses: the `context` law for a
context value (`AnyhowStrCtxLaw`, it keeps an `Ok`), and the outcomes that `htarget` names and of
the view. -/
theorem check_grant_permission_deref_fail (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (ctx : keystore2_selinux.Context)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error) (hc : contextCStr ctx = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  exact grant_tail_deref_fail caller_ctx access_vec ctx x hc

/-- conditional: the target is `c` and the check of `Grant` fails with `x`. The
result is `fail x`, whatever `access_vec` is. Hypotheses: the `context` law for a context value
(`AnyhowStrCtxLaw`), and the outcomes that `htarget` names, of the view of `ctx` and of
`check_permission` for `Grant`. -/
theorem check_grant_permission_grant_check_fail (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  exact grant_tail_check_fail caller_ctx access_vec ctx c hc x hcheck

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, and `access_vec` has bit 3
set (the value of `Grant`). The result is an error whose root cause is
`selinux::Error::PermissionDenied`. In the Rust source this path returns before the loop over the
permissions. Hypotheses: the `context`
of `check_grant_permission_grant_check_err`, the `context` law for a SELinux error
(`SelinuxStrCtxLaw`), and the outcomes `htarget` names and of `check_permission` for
`Grant`. -/
theorem check_grant_permission_grant_in_set (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hsel : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : HasBit access_vec 3) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = deniedRoot := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  exact grant_tail_in_set root hctxU hsel caller_ctx access_vec ctx c hc hcheck hbit

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, `access_vec` has no bit set
(the empty set), and bit 3 is therefore not set. The result is `Ok`. The loop over the permissions
has no iteration, so the statement has no `format` hypothesis. Hypotheses: the `context` laws of
`check_grant_permission_grant_check_err`, and the outcomes `htarget` names and of the view of
`ctx` and of `check_permission` for `Grant`. -/
theorem check_grant_permission_ok_empty (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hempty : ∀ i, i < 32 → ¬ HasBit access_vec i) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Ok ()) := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  have hbit : ¬ HasBit access_vec 3 := hempty 3 (by omega)
  rw [grant_tail_loop root hctxU caller_ctx access_vec ctx c hc hcheck hbit]
  exact grant_loop_done caller_ctx ctx _ _
    (grant_body_none caller_ctx ctx _ (by simp) (fun j _ hj32 hb => hempty j hj32 hb))

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, bit 3 of `access_vec` is not
set, and for every set bit `i` the check of the permission `KeyPerm::from(1 << i)` returns `Ok`.
The result is `Ok`. The set may be empty: the result is the same, and
`check_grant_permission_ok_empty` gives that case without the `format` law. Two set bits that are
no `KeyPerm` give two checks of `KeyPerm::None`: the statement covers the runs in which both give
the same answer (`Ok`). A run in which the policy answer changes between the two calls is outside
the model. Hypotheses: the `context` laws of `check_grant_permission_grant_check_err`, the `format`
law (`AllocFmtFormatSpec`, the loop builds a message in every iteration), the `context` law for
`()` with a `String` message (`AnyhowStringCtxLaw`, it keeps an `Ok`), and the outcomes `htarget`
names and of the view of `ctx` and of the calls of `check_permission`. -/
theorem check_grant_permission_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (hloop : ∀ i, i < 32 → HasBit access_vec i → ∃ kp, keyPermFromI32 (bitVal i) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ())) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Ok ()) := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  rw [grant_tail_loop root hctxU caller_ctx access_vec ctx c hc hcheck hbit]
  exact grant_loop_ok hfmt root hctxS caller_ctx ctx c hc _ { vec := access_vec, pos := 0#u8 }
    rfl (by simp) (fun j _ hj32 hb => hloop j hj32 hb)

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, bit 3 of `access_vec` is not
set, `i` is a set bit, the checks of the permissions of the set bits below `i` return `Ok`, and the
check of the permission of bit `i` returns an error `e`. No earlier check is for the same
permission: otherwise the failing call would repeat an earlier call with the same
arguments, and the model gives both calls the same outcome, so `hlow` and `hbad` would contradict
each other. For a bit that is no `KeyPerm`, this says `i` is the
lowest such set bit. The result is an error with the same root
cause as `e`. In the Rust source this path returns at the first failing check, so the bits above
`i` do not matter to the result. Hypotheses: the `context` laws of
`check_grant_permission_ok`, the `format` law (`AllocFmtFormatSpec`, the failing iteration builds
its message before `context`), and the outcomes that `htarget` names and of the calls of
`check_permission`. -/
theorem check_grant_permission_loop_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (i : Nat) (hi : i < 32) (hset : HasBit access_vec i)
    (hlow : ∀ j, j < i → HasBit access_vec j → ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ()))
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (e : anyhow.Error)
    (hbad : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
      ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  rw [grant_tail_loop root hctxU caller_ctx access_vec ctx c hc hcheck hbit]
  exact grant_loop_first hfmt root hctxS caller_ctx ctx c hc
    (fun r => ∃ e', r = ok (.Err e') ∧ root e' = root e) access_vec i hi hset hlow
    (fun it _ hnb => by
      obtain ⟨e', hb, hr⟩ := grant_body_some_err (hfmt _) caller_ctx ctx c hc it i hnb kp hkp e
        hbad root hctxS
      exact ⟨e', grant_loop_done caller_ctx ctx it _ hb, hr⟩)
    _ { vec := access_vec, pos := 0#u8 } rfl (by simp) rfl

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, bit 3 of `access_vec` is not
set, `i` is a set bit, the checks of the permissions of the set bits below `i` return `Ok`, and the check of the permission of bit `i` fails with `x`. The result is `fail x`. Hypotheses: the `context` laws of
`check_grant_permission_ok`, the `format` law (`AllocFmtFormatSpec`, the iterations below `i` build
a message before `context`; the law is used only when a lower bit is set), and the outcomes that
`htarget` names, of the view of `ctx` and of the calls of `check_permission`. -/
theorem check_grant_permission_loop_fail (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (i : Nat) (hi : i < 32) (hset : HasBit access_vec i)
    (hlow : ∀ j, j < i → HasBit access_vec j → ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ()))
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp)
    (x : Error)
    (hbad : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
      fail x) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = fail x := by
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget]
  rw [grant_tail_loop root hctxU caller_ctx access_vec ctx c hc hcheck hbit]
  exact grant_loop_first hfmt root hctxS caller_ctx ctx c hc
    (fun r => r = fail x) access_vec i hi hset hlow
    (fun it _ hnb => grant_loop_fail caller_ctx ctx it x
      (grant_body_some_fail caller_ctx ctx c hc it i hnb kp hkp x hbad))
    _ { vec := access_vec, pos := 0#u8 } rfl (by simp) rfl

/-- conditional: the function returns `Ok`. Then the access vector does not have bit 3 set (the
value of `Grant`), the key domain is `APP` with the caller uid equal to the namespace and `getcon`
returning the target `ctx`, or `SELINUX` with the lookup returning `ctx`, the view of `ctx` is
`c`, the check of `Grant` against `c` returned `Ok`, and for every set bit `i` the check of
`KeyPerm::from(1 << i)` against `c` returned `Ok`. Every other branch of the body ends in an error
under the laws: the foreign `APP` branch, the branch of an access vector with `Grant`, and the
other domains build an error through `context`, and a failed `getcon`, lookup, `Grant` check or
loop check goes to `from_residual`. Hypotheses: the `context` laws for a context value and for
`()` with a `&str` message (`AnyhowStrCtxLaw`), for `()` with a `String` message
(`AnyhowStringCtxLaw`), for a SELinux error with a `&str` message (`SelinuxStrCtxLaw`) and for a
keystore2 error with a `String` message (`KsStringCtxLaw`), and the outcome of the call. -/
theorem check_grant_permission_of_ok (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (hsel : SelinuxStrCtxLaw root) (hks : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (hok : permission.check_grant_permission caller_uid caller_ctx access_vec key =
      ok (.Ok ())) :
    ¬ HasBit access_vec 3 ∧
      ∃ ctx c, contextCStr ctx = ok c ∧
        ((key.domain = domainApp ∧ caller_uid = key.nspace ∧
            keystore2_selinux.getcon = ok (.Ok ctx)) ∨
          (key.domain = domainSelinux ∧
            permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))) ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
          permission.KeyPerm.Grant = ok (.Ok ()) ∧
        ∀ i, i < 32 → HasBit access_vec i → ∃ kp, keyPermFromI32 (bitVal i) = ok kp ∧
          keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
            ok (.Ok ()) := by
  obtain ⟨ctx, htarget⟩ := grant_front_inv root hctxC hsel hks caller_uid caller_ctx access_vec
    key hok
  rw [grant_eq_tail root hctxC caller_uid caller_ctx access_vec key ctx htarget] at hok
  obtain ⟨hbit, c, hc, hcheck, hall⟩ :=
    grant_tail_inv root hctxU hctxS hsel caller_ctx access_vec ctx hok
  exact ⟨hbit, ctx, c, hc, htarget, hcheck, hall⟩

end Keystore2Verify.Permission
