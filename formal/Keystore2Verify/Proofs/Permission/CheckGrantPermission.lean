import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open Keystore2Verify.Externals
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
`CStr`, and `AppSelinuxTarget caller_uid key c` says that step 1 succeeded with the target `c`.
A hypothesis about a call of `check_permission` for the permission `p` is a hypothesis about that
call only. Two bits that give the same `KeyPerm` (all the bits that are no `KeyPerm` give `None`)
refer to the same call, and a theorem that assumes different outcomes for them has no instance. -/

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
  sorry

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
  sorry

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
  sorry

/-- conditional: the domain is neither `APP` nor `SELINUX` (`GRANT`, `BLOB`, `KEY_ID` and every
other number). The result is an error whose root cause is the keystore2 error with the response
code `SYSTEM_ERROR`. No uid is compared and no SELinux check is made. Hypotheses: the `format`
law (`AllocFmtFormatSpec`), and the `context` law for a keystore2 error with a `String` message
(`KsStringCtxLaw`). -/
theorem check_grant_permission_other_domain (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc)
    (happ : key.domain ≠ domainApp) (hsel : key.domain ≠ domainSelinux) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = .ks sysError := by
  sorry

/-- conditional: the target is `c` and the check of `Grant` returns an error `e`. The result is an
error with the same root cause as `e`, whatever `access_vec` is. Hypotheses: the `context` laws
for a context value and for `()` with a `&str` message (`AnyhowStrCtxLaw`), and the outcomes that
`AppSelinuxTarget` names and the outcome of `check_permission` for `Grant`. -/
theorem check_grant_permission_grant_check_err (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (htarget : AppSelinuxTarget caller_uid key c) (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, and `access_vec` has bit 3
set (the value of `Grant`). The result is an error whose root cause is
`selinux::Error::PermissionDenied`. No other permission is checked. Hypotheses: the `context`
laws of `check_grant_permission_grant_check_err`, the `context` law for a SELinux error
(`SelinuxStrCtxLaw`), and the outcomes that `AppSelinuxTarget` names and of `check_permission` for
`Grant`. -/
theorem check_grant_permission_grant_in_set (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hsel : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (htarget : AppSelinuxTarget caller_uid key c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : HasBit access_vec 3) :
    ∃ e, permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Err e) ∧
      root e = deniedRoot := by
  sorry

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, bit 3 of `access_vec` is not
set, and for every set bit `i` the check of the permission `KeyPerm::from(1 << i)` returns `Ok`.
The result is `Ok`. With the empty set no check is made in the loop. Hypotheses: the `context`
laws of `check_grant_permission_grant_check_err`, the `context` law for `()` with a `String`
message (`AnyhowStringCtxLaw`), and the outcomes that `AppSelinuxTarget` names and of the calls of
`check_permission`. -/
theorem check_grant_permission_ok (root : anyhow.Error → ErrRoot)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (htarget : AppSelinuxTarget caller_uid key c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (hloop : ∀ i, i < 32 → HasBit access_vec i → ∃ kp, keyPermFromI32 (bitVal i) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ())) :
    permission.check_grant_permission caller_uid caller_ctx access_vec key = ok (.Ok ()) := by
  sorry

/-- conditional: the target is `c`, the check of `Grant` returns `Ok`, bit 3 of `access_vec` is not
set, `i` is a set bit, the checks of the permissions of the set bits below `i` return `Ok`, and the
check of the permission of bit `i` returns an error `e`. The result is an error with the same root
cause as `e`. The bits above `i` are not checked. Hypotheses: the `context` laws of
`check_grant_permission_ok`, the `format` law (`AllocFmtFormatSpec`), and the outcomes that
`AppSelinuxTarget` names and of the calls of `check_permission`. -/
theorem check_grant_permission_loop_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec)
    (hctxC : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (hctxU : AnyhowStrCtxLaw root Unit) (hctxS : AnyhowStringCtxLaw root Unit)
    (caller_uid : utils.AppUid) (caller_ctx : CStr)
    (access_vec : permission.KeyPermSet) (key : KeyDesc) (c : CStr)
    (htarget : AppSelinuxTarget caller_uid key c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.Grant = ok (.Ok ()))
    (hbit : ¬ HasBit access_vec 3)
    (i : Nat) (hi : i < 32) (hset : HasBit access_vec i)
    (hlow : ∀ j, j < i → HasBit access_vec j → ∃ kp, keyPermFromI32 (bitVal j) = ok kp ∧
      keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
        ok (.Ok ()))
    (kp : permission.KeyPerm) (hkp : keyPermFromI32 (bitVal i) = ok kp) (e : anyhow.Error)
    (hbad : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c kp =
      ok (.Err e)) :
    ∃ e', permission.check_grant_permission caller_uid caller_ctx access_vec key =
        ok (.Err e') ∧ root e' = root e := by
  sorry

end Keystore2Verify.Permission
