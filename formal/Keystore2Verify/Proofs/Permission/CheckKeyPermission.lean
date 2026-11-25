import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open Keystore2Verify.Externals
open permission.KeyPerm.Insts

/-! `check_key_permission` works in this order, and a failing step returns at once:

0. If the access vector is `some av` and `av` includes `perm`, the result is `Ok`. In the Rust
   source this path returns before the domain is looked at.
1. Otherwise, by the domain of the key, it computes the target context. `APP`: the caller uid must
   equal the namespace, and the target is the context of `getcon`. `SELINUX`: the target is the
   lookup of the namespace. `BLOB`: the same lookup, and the caller must also hold `ManageBlob` for
   it. `GRANT`, `KEY_ID` and every other number: an error.
2. The caller must hold `perm` for the target, and the result of that check is the result.

`Covers perm access_vector` says that step 0 applies. The theorems about steps 1 and 2 assume that
it does not (`¬ Covers perm access_vector`): this includes `access_vector = none`.
In the theorems, `contextCStr ctx = ok c` says that the context `ctx` has the view `c` as a
`CStr`.
A hypothesis about a call of `check_permission` is a hypothesis about that call only. The
translation models a repeated call with the same arguments as one pure function, so two calls with
the same arguments have the same outcome in every statement. For the domain `BLOB` with
`perm = ManageBlob`, step 1 and step 2 make the same call. The success statement covers this case:
it covers the runs in which the repeated check gives the same answer each time (`Ok`). A run in
which the policy answer changes between the two calls is outside the model. The final-check error and failure statements need no separate `perm ≠ ManageBlob` hypothesis:
when `perm = ManageBlob`, the same call cannot both succeed and return the later error or failure.
Where a statement says that an outcome is `fail x`, the generated function returns `fail x` at once. The statements about `fail` for the lookup and for `getcon` need no law: the
generated body binds these results first. -/

/-- exact: the access vector is `some av` and `av` includes the bit set of `perm`. The result is
`Ok`, for every domain (`GRANT`, `KEY_ID` and unknown numbers included), every caller uid and
every caller context. In the Rust source this path returns before any external function is
called. -/
theorem check_key_permission_covered
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hcov : Covers perm access_vector) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = ok (.Ok ()) := by
  sorry

/-- exact: `perm` is `KeyPerm::None` and the access vector is `some av`, for any `av`. The result is
`Ok`, for every domain. This is the case where `perm` has the empty bit set. -/
theorem check_key_permission_none_perm
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (key : KeyDesc)
    (av : permission.KeyPermSet) :
    permission.check_key_permission caller_uid caller_ctx permission.KeyPerm.None key (some av) =
      ok (.Ok ()) := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `APP`, and the caller uid
differs from the namespace. The result is an error whose root cause is
`selinux::Error::PermissionDenied`. Hypothesis: the `context` law for a SELinux error with a
`&str` message (`SelinuxStrCtxLaw`). -/
theorem check_key_permission_foreign_app (root : anyhow.Error → ErrRoot)
    (hctx : SelinuxStrCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainApp) (hne : caller_uid ≠ key.nspace) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e) ∧ root e = deniedRoot := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `APP`, the caller uid
equals the namespace, and `getcon` returns an error `e`. The result is an error with the same root
cause as `e`. Hypotheses: the `from_str_nonconst` and `format` laws
(`CoreFmtArgumentsFromStrNonconstSpec`, `AllocFmtFormatSpec`), the `context` law for an
`anyhow::Error` result with a `String` message and a context value (`AnyhowStringCtxLaw`), and the
outcome of `getcon`. -/
theorem check_key_permission_app_getcon_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (e : anyhow.Error) (hget : keystore2_selinux.getcon = ok (.Err e)) :
    ∃ e', permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `SELINUX` or `BLOB`, and
the lookup of the namespace returns an error `e`. The result is an error with the same root cause
as `e`. In the Rust source this path returns before the uid is compared (`SELINUX`, `BLOB`) and
before `check_permission` is called for `BLOB`. Hypotheses:
the laws of `check_key_permission_app_getcon_err`, and the outcome of the lookup. -/
theorem check_key_permission_lookup_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainSelinux ∨ key.domain = domainBlob)
    (e : anyhow.Error) (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Err e)) :
    ∃ e', permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `APP`, the caller uid
equals the namespace, and `getcon` fails with `x`. The result is `fail x`.
Hypothesis: the outcome of `getcon`. No law is needed. -/
theorem check_key_permission_app_getcon_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainApp) (heq : caller_uid = key.nspace)
    (x : Error) (hget : keystore2_selinux.getcon = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `SELINUX` or `BLOB`, and
the namespace lookup returns `fail x`. The caller returns the same `fail x`; the statement does
not identify the cause of the opaque lookup failure. Hypothesis: the outcome of the lookup. No law is needed. -/
theorem check_key_permission_lookup_fail
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (hdom : key.domain = domainSelinux ∨ key.domain = domainBlob)
    (x : Error) (hlook : permission.lookup_keystore2_key_context key.nspace = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `GRANT`, and the access
vector is `some av`. The result is an error whose root cause is
`selinux::Error::PermissionDenied`. Hypotheses: the `format` law (`AllocFmtFormatSpec`), and the
`context` law for a SELinux error with a `String` message (`SelinuxStringCtxLaw`). -/
theorem check_key_permission_grant_not_granted (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : SelinuxStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (av : permission.KeyPermSet)
    (hnc : ¬ Covers perm (some av)) (hdom : key.domain = domainGrant) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key (some av) =
        ok (.Err e) ∧ root e = deniedRoot := by
  sorry

/-- conditional: the domain is `GRANT` and there is no access vector. The result is an error whose
root cause is the keystore2 error with the response code `SYSTEM_ERROR`. Hypotheses: the
`from_str_nonconst` and `format` laws, and the `context` law for a keystore2 error with a `String`
message (`KsStringCtxLaw`). -/
theorem check_key_permission_grant_no_vector (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (hdom : key.domain = domainGrant) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key none = ok (.Err e) ∧
      root e = .ks sysError := by
  sorry

/-- conditional: the access vector does not cover `perm` and the domain is `KEY_ID`. The result is
an error whose root cause is the keystore2 error with the response code `SYSTEM_ERROR`.
Hypotheses: the laws of `check_key_permission_grant_no_vector`. -/
theorem check_key_permission_key_id (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainKeyId) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e) ∧ root e = .ks sysError := by
  sorry

/-- conditional: the access vector does not cover `perm` and the domain is not one of the five
named numbers 0 to 4 (a negative number, or 5 and above). The result is an error whose root cause
is the keystore2 error with the response code `INVALID_ARGUMENT`. Hypotheses: the `format` law
(`AllocFmtFormatSpec`), and the `context` law for a keystore2 error with a `String` message
(`KsStringCtxLaw`). -/
theorem check_key_permission_unknown_domain (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hctx : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (h0 : key.domain ≠ domainApp) (h1 : key.domain ≠ domainGrant)
    (h2 : key.domain ≠ domainSelinux) (h3 : key.domain ≠ domainBlob)
    (h4 : key.domain ≠ domainKeyId) :
    ∃ e, permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e) ∧ root e = .ks invalidArgumentError := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `BLOB`, the lookup returns
the context `ctx`, and the check of `ManageBlob` returns an error `e`. The function returns the
same error `e`. In the Rust source this path returns before the check of `perm`. Hypotheses: the
laws of `check_key_permission_app_getcon_err` (the `context` call of the lookup keeps the `Ok`),
and the outcomes of the lookup, of the view of `ctx`, and of `check_permission` for
`ManageBlob`. -/
theorem check_key_permission_blob_manage_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr) (e : anyhow.Error)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Err e)) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Err e) := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `APP` (the uid equals the
namespace and `getcon` returns `ctx`) or `SELINUX` (the lookup returns `ctx`), and the check of
`perm` against the view `c` of `ctx` returns `Ok`. The result is `Ok`. Hypotheses: the
`from_str_nonconst` and `format` laws, the `context` law of `check_key_permission_app_getcon_err`,
and the outcomes of `getcon` or the lookup, of the view of `ctx`, and of the check of `perm`. -/
theorem check_key_permission_app_selinux_check_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ()) := by
  sorry

/-- conditional: the same as `check_key_permission_app_selinux_check_ok`, but the check of `perm`
returns an error `e`. The function returns the same error `e`. Hypotheses: the same. -/
theorem check_key_permission_app_selinux_check_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Err e) := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `BLOB`, the lookup returns
`ctx`, the check of `ManageBlob` against the view `c` of `ctx` returns `Ok`, and the check of
`perm` against `c` returns `Ok`. The result is `Ok`. For `perm = ManageBlob` the two checks are the
same call: the statement covers the runs in which it gives the same answer (`Ok`) both times. A
run in which the policy answer changes between the two calls is outside the model. Hypotheses: the
laws of `check_key_permission_app_selinux_check_ok`, and the outcomes of the lookup, of the view
of `ctx`, and of the two checks. -/
theorem check_key_permission_blob_check_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Ok ()))
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ()) := by
  sorry

/-- conditional: the same as `check_key_permission_blob_check_ok`, but the check of `perm` returns
an error `e`. The function returns the same error `e`. `perm` is not `ManageBlob`: for
`perm = ManageBlob` the hypotheses `hmanage` and `hcheck` would contradict each other (one call,
two outcomes). Hypotheses: the same. -/
theorem check_key_permission_blob_check_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Ok ()))
    (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Err e) := by
  sorry

/-- conditional: the access vector does not cover `perm`, the target is `ctx` (`APP` with the uid
equal to the namespace and `getcon` returning `ctx`, or `SELINUX` with the lookup returning
`ctx`), and the view of `ctx` as a `CStr` fails with `x`. The result is `fail x`.
Hypotheses: the `from_str_nonconst` and `format` laws and the `context` law of
`check_key_permission_app_getcon_err` (the message is built before the view, and the `context`
keeps an `Ok`), and the outcomes of `getcon` or the lookup and of the view. -/
theorem check_key_permission_app_selinux_deref_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector)
    (ctx : keystore2_selinux.Context)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error) (hc : contextCStr ctx = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the same as `check_key_permission_app_selinux_check_ok`, but the check of `perm`
fails with `x`. The result is `fail x`. Hypotheses: the same. -/
theorem check_key_permission_app_selinux_check_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (ctx : keystore2_selinux.Context) (hc : contextCStr ctx = ok c)
    (htarget : (key.domain = domainApp ∧ caller_uid = key.nspace ∧
        keystore2_selinux.getcon = ok (.Ok ctx)) ∨
      (key.domain = domainSelinux ∧
        permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)))
    (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `BLOB`, the lookup returns
`ctx`, and the view of `ctx` as a `CStr` fails with `x`. The result is `fail x`.
Hypotheses: the laws of `check_key_permission_app_selinux_deref_fail`, and the outcomes of the
lookup and of the view. -/
theorem check_key_permission_blob_deref_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (x : Error) (hc : contextCStr ctx = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the access vector does not cover `perm`, the domain is `BLOB`, the lookup returns
`ctx`, and the check of `ManageBlob` against the view `c` of `ctx` fails with `x`.
The result is `fail x`. Hypotheses: the laws of `check_key_permission_app_selinux_deref_fail`,
and the outcomes of the lookup, of the view of `ctx`, and of `check_permission` for
`ManageBlob`. -/
theorem check_key_permission_blob_manage_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr) (x : Error)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the same as `check_key_permission_blob_check_err`, but the check of `perm` fails
with `x`. The result is `fail x`. `perm` is not `ManageBlob`: otherwise `hmanage`
and `hcheck` would contradict each other. Hypotheses: the same. -/
theorem check_key_permission_blob_check_fail (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (hdom : key.domain = domainBlob)
    (ctx : keystore2_selinux.Context) (c : CStr)
    (hlook : permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx))
    (hc : contextCStr ctx = ok c)
    (hmanage : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      permission.KeyPerm.ManageBlob = ok (.Ok ()))
    (x : Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = fail x) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector = fail x := by
  sorry

/-- conditional: the function returns `Ok`. Then the access vector covers `perm`, or the target is
`ctx`, the view of `ctx` is `c`, the check of `perm` against `c` returned `Ok`, and one of three
paths was taken: `APP` with the uid equal to the namespace and `getcon` returning `ctx`, `SELINUX`
with the lookup returning `ctx`, or `BLOB` with the lookup returning `ctx` and the check of
`ManageBlob` against `c` returning `Ok`. The access vector may cover `perm` for every domain, so
the first case says nothing about the domain. Every other branch of the body ends in an error
under the laws: the `GRANT`, `KEY_ID` and unknown-domain branches and the foreign `APP` branch
build an error through `context`, and a failed `getcon`, lookup or `ManageBlob` check goes to
`from_residual`. Hypotheses: the `context` laws for a context value with a `String` message
(`AnyhowStringCtxLaw`), for a SELinux error with a `&str` and with a `String` message
(`SelinuxStrCtxLaw`, `SelinuxStringCtxLaw`) and for a keystore2 error with a `String` message
(`KsStringCtxLaw`), and the outcome of the call. -/
theorem check_key_permission_of_ok (root : anyhow.Error → ErrRoot)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (hselStr : SelinuxStrCtxLaw root) (hselString : SelinuxStringCtxLaw root)
    (hks : KsStringCtxLaw root)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hok : permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ())) :
    Covers perm access_vector ∨
      ∃ ctx c, contextCStr ctx = ok c ∧
        keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c perm =
          ok (.Ok ()) ∧
        ((key.domain = domainApp ∧ caller_uid = key.nspace ∧
            keystore2_selinux.getcon = ok (.Ok ctx)) ∨
          (key.domain = domainSelinux ∧
            permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx)) ∨
          (key.domain = domainBlob ∧
            permission.lookup_keystore2_key_context key.nspace = ok (.Ok ctx) ∧
            keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
              permission.KeyPerm.ManageBlob = ok (.Ok ()))) := by
  sorry

end Keystore2Verify.Permission
