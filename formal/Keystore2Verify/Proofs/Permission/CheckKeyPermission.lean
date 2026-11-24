import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open Keystore2Verify.Externals
open permission.KeyPerm.Insts

/-! `check_key_permission` works in this order, and a failing step returns at once:

0. If the access vector is `some av` and `av` includes `perm`, the result is `Ok`. Nothing else is
   looked at, not even the domain.
1. Otherwise, by the domain of the key, it computes the target context. `APP`: the caller uid must
   equal the namespace, and the target is the context of `getcon`. `SELINUX`: the target is the
   lookup of the namespace. `BLOB`: the same lookup, and the caller must also hold `ManageBlob` for
   it. `GRANT`, `KEY_ID` and every other number: an error.
2. The caller must hold `perm` for the target, and the result of that check is the result.

`Covers perm access_vector` says that step 0 applies. The theorems about steps 1 and 2 assume that
it does not (`¬ Covers perm access_vector`): this includes `access_vector = none`.
In the theorems, `contextCStr ctx = ok c` says that the context `ctx` has the view `c` as a
`CStr`, `AppSelinuxTarget` and `BlobTarget` say that step 1 succeeded with the target `c`.
A hypothesis about a call of `check_permission` is a hypothesis about that call only. For the
domain `BLOB` with `perm = KeyPerm.ManageBlob` the two checks are the same call, and a theorem
that assumes different outcomes for them has no instance. -/

/-- exact: the access vector is `some av` and `av` includes the bit set of `perm`. The result is
`Ok`, for every domain (`GRANT`, `KEY_ID` and unknown numbers included), every caller uid and
every caller context. Nothing external is called. -/
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
as `e`. The uid is not compared, and for `BLOB` the check of `ManageBlob` is not run. Hypotheses:
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
the context `ctx`, and the check of `ManageBlob` returns an error `e`. The result is an error with
the same root cause as `e`: no message is added, and the check of `perm` is not run. Hypotheses:
the laws of `check_key_permission_app_getcon_err`, and the outcomes of the lookup, of the view of
`ctx`, and of `check_permission` for `ManageBlob`. -/
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
    ∃ e', permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: the access vector does not cover `perm`, the target is `c`, and the check of
`perm` against `c` returns `Ok`. The result is `Ok`. The target is `c` as `AppSelinuxTarget` or
`BlobTarget` say. Hypotheses: the `from_str_nonconst` and `format` laws, the `context` law of
`check_key_permission_app_getcon_err`, and the outcomes those two definitions name and of the
check of `perm`. -/
theorem check_key_permission_check_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (htarget : AppSelinuxTarget caller_uid key c ∨ BlobTarget caller_ctx key c)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Ok ())) :
    permission.check_key_permission caller_uid caller_ctx perm key access_vector =
      ok (.Ok ()) := by
  sorry

/-- conditional: the access vector does not cover `perm`, the target is `c`, and the check of
`perm` against `c` returns an error `e`. The result is an error with the same root cause as `e`:
no message is added. Hypotheses: the same as `check_key_permission_check_ok`. -/
theorem check_key_permission_check_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyhowStringCtxLaw root keystore2_selinux.Context)
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (perm : permission.KeyPerm)
    (key : KeyDesc) (access_vector : Option permission.KeyPermSet)
    (hnc : ¬ Covers perm access_vector) (c : CStr)
    (htarget : AppSelinuxTarget caller_uid key c ∨ BlobTarget caller_ctx key c)
    (e : anyhow.Error)
    (hcheck : keystore2_selinux.check_permission Keystore2_selinuxClassPermission caller_ctx c
      perm = ok (.Err e)) :
    ∃ e', permission.check_key_permission caller_uid caller_ctx perm key access_vector =
        ok (.Err e') ∧ root e' = root e := by
  sorry

end Keystore2Verify.Permission
