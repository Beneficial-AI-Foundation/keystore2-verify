import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open Keystore2Verify.Externals
open permission.KeystorePerm.Insts

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
  sorry

/-- conditional: if `getcon` returns an error `e`, the function returns an error with the same
root cause as `e`, and the check is not run. Hypotheses: the `context` law of
`check_keystore_permission_ok`, and the outcome of `getcon`. -/
theorem check_keystore_permission_getcon_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_keystore_permission caller_ctx perm = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if `getcon` returns the context `ctx` and the check of `perm` returns an error
`e`, the function returns an error with the same root cause as `e`: no message is added.
Hypotheses: the `context` law of `check_keystore_permission_ok`, and the outcomes of `getcon`, of
the view of `ctx`, and of `check_permission`. -/
theorem check_keystore_permission_check_err (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStrCtxLaw root keystore2_selinux.Context)
    (caller_ctx : CStr) (perm : permission.KeystorePerm)
    (ctx : keystore2_selinux.Context) (c : CStr) (e : anyhow.Error)
    (hget : keystore2_selinux.getcon = ok (.Ok ctx)) (hc : contextCStr ctx = ok c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    ∃ e', permission.check_keystore_permission caller_ctx perm = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if `getcon` panics, the function panics in the same way, and the check is not
run. Hypothesis: the outcome of `getcon`. No law is needed. -/
theorem check_keystore_permission_getcon_fail (caller_ctx : CStr)
    (perm : permission.KeystorePerm) (x : Error)
    (hget : keystore2_selinux.getcon = fail x) :
    permission.check_keystore_permission caller_ctx perm = fail x := by
  sorry

/-- conditional: if `getcon` returns the context `ctx` and the check of `perm` panics, the
function panics in the same way. Hypotheses: the `context` law of
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
  sorry

end Keystore2Verify.Permission
