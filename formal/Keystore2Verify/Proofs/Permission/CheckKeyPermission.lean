import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open Keystore2Verify.Externals
open core.result.Result.Insts core.convert core.fmt.rt
open Aeneas.Std.core.fmt.Arguments renaming new → argumentsNew
open permission.KeyPermSet.Insts
open permission.KeyPerm.Insts
open permission.KeyPermSet.Insts.CoreConvertFromKeyPerm renaming «from» → setFromKeyPerm

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
  obtain ⟨s, o, rfl, ho, hinc⟩ := hcov
  have hb : (s &&& o = o) = True := eq_true hinc
  unfold permission.check_key_permission
  simp [permission.KeyPermSet.includes, ho, lift, hb]

/-- exact: `perm` is `KeyPerm::None` and the access vector is `some av`, for any `av`. The result is
`Ok`, for every domain. This is the case where `perm` has the empty bit set. -/
theorem check_key_permission_none_perm
    (caller_uid : utils.AppUid) (caller_ctx : CStr) (key : KeyDesc)
    (av : permission.KeyPermSet) :
    permission.check_key_permission caller_uid caller_ctx permission.KeyPerm.None key (some av) =
      ok (.Ok ()) := by
  have hz : setFromKeyPerm permission.KeyPerm.None = ok 0#i32 := by
    simp [setFromKeyPerm, lift]; rfl
  unfold permission.check_key_permission
  have hz2 : av &&& 0#i32 = 0#i32 := I32.bv_eq_imp_eq _ _ (by simp)
  simp [permission.KeyPermSet.includes, hz, lift, hz2]

/-- Peel the first step off a successful `do` block: the bound computation succeeded. -/
private theorem bind_ok_inv {α β : Type} {c : Result α} {f : α → Result β} {y : β}
    (h : (do let a ← c; f a) = ok y) : ∃ a, c = ok a ∧ f a = ok y := by
  cases c with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

/-- `ok` is injective. -/
private theorem ok_inj {α : Type} {a b : α} (h : (ok a : Result α) = ok b) : a = b := by
  simpa using h

/-- A `context` call that satisfies the law and receives an `Err` does not return `Ok`. -/
private theorem ctx_err_not_ok {T E Er C : Type} {rE : E → ErrRoot} {rt : Er → ErrRoot}
    {ctx : core.result.Result T E → C → Result (core.result.Result T Er)}
    (hl : ResultContextLaw rE rt ctx) (x : E) (c : C) (v : T) :
    ctx (.Err x) c ≠ ok (.Ok v) := by
  obtain ⟨e, he, -⟩ := hl.2 x c
  rw [he]; simp

/-- If `s` does not cover `perm`, `includes` of the `KeyPerm` conversion returns `false`. -/
private theorem includes_false (perm : permission.KeyPerm) (s : permission.KeyPermSet)
    (hnc : ¬ Covers perm (some s)) :
    permission.KeyPermSet.includes
        (core.convert.IntoFrom CoreConvertFromKeyPerm) s perm =
      ok false := by
  obtain ⟨o, ho⟩ : ∃ o, setFromKeyPerm perm = ok o :=
    ⟨IScalar.cast .I32 (read_discriminant perm), by simp [setFromKeyPerm, lift]⟩
  have hn : ¬ s &&& o = o := fun h => hnc ⟨s, o, rfl, ho, h⟩
  simp [permission.KeyPermSet.includes, ho, lift, hn]

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
  obtain ⟨e, he, hr⟩ := hctx.2 keystore2_selinux.Error.PermissionDenied
    (toStr "Trying to access key without ownership.")
  refine ⟨e, ?_, by rw [hr]; rfl⟩
  have hne' : (caller_uid != key.nspace) = true := by simpa using hne
  have hd : key.domain = (0#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s
  · unfold permission.check_key_permission
    simp [hd, hne', keystore2_selinux.Error.perm, he]
  · have hn := includes_false perm s hnc
    unfold permission.check_key_permission
    simp [hn, hd, hne', keystore2_selinux.Error.perm, he]

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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/permission.rs:367: getcon failed.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨e', he', hr⟩ := hctx.2 e s1
  refine ⟨e', ?_, hr⟩
  have hd : key.domain = (0#iscalar : Std.I32) := hdom
  have hne : (caller_uid != key.nspace) = false := by simp [heq]
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hne, hget, h1, f1, he',
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:370: Domain::SELINUX: Failed to \
      lookup namespace.")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨s2, f2⟩ := hfmt a2
  obtain ⟨e1, he1, hr1⟩ := hctx.2 e s1
  obtain ⟨e2, he2, hr2⟩ := hctx.2 e s2
  have hd' : key.domain = (2#iscalar : Std.I32) ∨ key.domain = (3#iscalar : Std.I32) := hdom
  rcases hd' with hd | hd
  · refine ⟨e1, ?_, hr1⟩
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, he1,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]
  · refine ⟨e2, ?_, hr2⟩
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h2, f2, he2,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  have hd : key.domain = (0#iscalar : Std.I32) := hdom
  have hne : (caller_uid != key.nspace) = false := by simp [heq]
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hne, hget,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  have hd' : key.domain = (2#iscalar : Std.I32) ∨ key.domain = (3#iscalar : Std.I32) := hdom
  rcases hd' with hd | hd <;>
  · rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨s1, f1⟩ := hfmt ()
  obtain ⟨e', he', hr⟩ := hctx.2 keystore2_selinux.Error.PermissionDenied s1
  refine ⟨e', ?_, hr⟩
  obtain ⟨n, hn⟩ : ∃ n, Keystore2_selinuxClassPermission.name perm =
      ok n := by cases perm <;> exact ⟨_, rfl⟩
  have hd : key.domain = (1#iscalar : Std.I32) := hdom
  unfold permission.check_key_permission
  simp [includes_false, hnc, hd, hn, f1, he', core.fmt.Arguments, Argument,
      keystore2_selinux.Error.perm,
      core.hint.must_use, argumentsNew, Argument.new_display,
      ]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:379: Cannot check permission \
      for Domain::GRANT without access vector.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨e', he', hr⟩ := hctx.2 sysError s1
  refine ⟨e', ?_, hr⟩
  simp only [sysError] at he'
  have hd : key.domain = (1#iscalar : Std.I32) := hdom
  unfold permission.check_key_permission
  simp [hd, h1, f1, he', error.Error.sys,
      core.hint.must_use, ]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:390: Cannot check permission \
      for Domain::KEY_ID.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨e', he', hr⟩ := hctx.2 sysError s1
  refine ⟨e', ?_, hr⟩
  simp only [sysError] at he'
  have hd : key.domain = (4#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, h1, f1, he', error.Error.sys,
      core.hint.must_use, ]

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
  obtain ⟨s1, f1⟩ := hfmt ()
  obtain ⟨e', he', hr⟩ := hctx.2 invalidArgumentError s1
  refine ⟨e', ?_, hr⟩
  simp only [invalidArgumentError] at he'
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, core.fmt.Arguments, Argument, f1, he',
      core.hint.must_use, argumentsNew, Argument.new_display,
      Argument.new_debug, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]
  all_goals split
  all_goals first
    | exact absurd (by assumption) h0
    | exact absurd (by assumption) h1
    | exact absurd (by assumption) h2
    | exact absurd (by assumption) h3
    | exact absurd (by assumption) h4
    | simp []

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  have hd : key.domain = (3#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, hctx.1, hc, hmanage,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/permission.rs:367: getcon failed.")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/permission.rs:370: Domain::SELINUX: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨s2, f2⟩ := hfmt a2
  rcases htarget with ⟨hd0, heq, hget⟩ | ⟨hd2, hlook⟩
  · have hd : key.domain = (0#iscalar : Std.I32) := hd0
    have hne : (caller_uid != key.nspace) = false := by simp [heq]
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hne, hget, h1, f1, hctx.1, hc, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]
  · have hd : key.domain = (2#iscalar : Std.I32) := hd2
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h2, f2, hctx.1, hc, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/permission.rs:367: getcon failed.")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/permission.rs:370: Domain::SELINUX: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨s2, f2⟩ := hfmt a2
  rcases htarget with ⟨hd0, heq, hget⟩ | ⟨hd2, hlook⟩
  · have hd : key.domain = (0#iscalar : Std.I32) := hd0
    have hne : (caller_uid != key.nspace) = false := by simp [heq]
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hne, hget, h1, f1, hctx.1, hc, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]
  · have hd : key.domain = (2#iscalar : Std.I32) := hd2
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h2, f2, hctx.1, hc, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  have hd : key.domain = (3#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, hctx.1, hc, hmanage, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  have hd : key.domain = (3#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, hctx.1, hc, hmanage, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/permission.rs:367: getcon failed.")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/permission.rs:370: Domain::SELINUX: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨s2, f2⟩ := hfmt a2
  rcases htarget with ⟨hd0, heq, hget⟩ | ⟨hd2, hlook⟩
  · have hd : key.domain = (0#iscalar : Std.I32) := hd0
    have hne : (caller_uid != key.nspace) = false := by simp [heq]
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hne, hget, h1, f1, hctx.1, hc,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]
  · have hd : key.domain = (2#iscalar : Std.I32) := hd2
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h2, f2, hctx.1, hc,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/permission.rs:367: getcon failed.")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/permission.rs:370: Domain::SELINUX: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨s2, f2⟩ := hfmt a2
  rcases htarget with ⟨hd0, heq, hget⟩ | ⟨hd2, hlook⟩
  · have hd : key.domain = (0#iscalar : Std.I32) := hd0
    have hne : (caller_uid != key.nspace) = false := by simp [heq]
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hne, hget, h1, f1, hctx.1, hc, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]
  · have hd : key.domain = (2#iscalar : Std.I32) := hd2
    rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h2, f2, hctx.1, hc, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  have hd : key.domain = (3#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, hctx.1, hc,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  have hd : key.domain = (3#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, hctx.1, hc, hmanage,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/permission.rs:394: Domain::BLOB: Failed to \
      lookup namespace.")
  obtain ⟨s1, f1⟩ := hfmt a1
  have hd : key.domain = (3#iscalar : Std.I32) := hdom
  rcases access_vector with _ | s <;> unfold permission.check_key_permission <;>
    simp [includes_false, hnc, hd, hlook, h1, f1, hctx.1, hc, hmanage, hcheck,
      core.hint.must_use, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from]

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
  by_cases hcov : Covers perm access_vector
  · exact Or.inl hcov
  right
  rcases access_vector with _ | s <;> unfold permission.check_key_permission at hok <;>
    simp [includes_false, hcov, core.hint.must_use, argumentsNew,
      Argument.new_debug, Argument.new_display] at hok
  · split at hok
    · rename_i _ hdm
      split at hok
      · rename_i hq
        obtain ⟨r, hr, hok⟩ := bind_ok_inv hok
        obtain ⟨_, _, hok⟩ := bind_ok_inv hok
        obtain ⟨s1, _, hok⟩ := bind_ok_inv hok
        obtain ⟨r1, hr1, hok⟩ := bind_ok_inv hok
        obtain ⟨cf, hcf, hok⟩ := bind_ok_inv hok
        rcases r with ctx | e
        · rw [hctx.1] at hr1
          obtain rfl := ok_inj hr1
          simp [CoreOpsTry.branch] at hcf
          obtain rfl := hcf
          simp only at hok
          obtain ⟨c, hc, hok⟩ := bind_ok_inv hok
          exact ⟨ctx, c, hc, hok, Or.inl ⟨hdm, IScalar.val_eq_imp _ _ hq, hr⟩⟩
        · obtain ⟨e', he', -⟩ := hctx.2 e s1
          rw [he'] at hr1
          obtain rfl := ok_inj hr1
          simp [CoreOpsTry.branch] at hcf
          obtain rfl := hcf
          simp [CoreOpsTry_traitFromResidualResult.from_residual,
            FromSame.from] at hok
      · obtain ⟨_, _, hok⟩ := bind_ok_inv hok
        exact absurd hok (ctx_err_not_ok hselStr _ _ _)
    · rename_i _ hdm
      obtain ⟨r, hr, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨s1, _, hok⟩ := bind_ok_inv hok
      obtain ⟨r1, hr1, hok⟩ := bind_ok_inv hok
      obtain ⟨cf, hcf, hok⟩ := bind_ok_inv hok
      rcases r with ctx | e
      · rw [hctx.1] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp only at hok
        obtain ⟨c, hc, hok⟩ := bind_ok_inv hok
        exact ⟨ctx, c, hc, hok, Or.inr (Or.inl ⟨hdm, hr⟩)⟩
      · obtain ⟨e', he', -⟩ := hctx.2 e s1
        rw [he'] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp [CoreOpsTry_traitFromResidualResult.from_residual,
          FromSame.from] at hok
    · rename_i _ hdm
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      exact absurd hok (ctx_err_not_ok hks _ _ _)
    · rename_i _ hdm
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      exact absurd hok (ctx_err_not_ok hks _ _ _)
    · rename_i _ hdm
      obtain ⟨r, hr, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨s1, _, hok⟩ := bind_ok_inv hok
      obtain ⟨r1, hr1, hok⟩ := bind_ok_inv hok
      obtain ⟨cf, hcf, hok⟩ := bind_ok_inv hok
      rcases r with ctx | e
      · rw [hctx.1] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp only at hok
        obtain ⟨c, hc, hok⟩ := bind_ok_inv hok
        obtain ⟨r2, hr2, hok⟩ := bind_ok_inv hok
        obtain ⟨cf1, hcf1, hok⟩ := bind_ok_inv hok
        rcases r2 with u | e2
        · cases u
          simp [CoreOpsTry.branch] at hcf1
          obtain rfl := hcf1
          simp only at hok
          exact ⟨ctx, c, hc, hok, Or.inr (Or.inr ⟨hdm, hr, hr2⟩)⟩
        · simp [CoreOpsTry.branch] at hcf1
          obtain rfl := hcf1
          simp [CoreOpsTry_traitFromResidualResult.from_residual,
            FromSame.from] at hok
      · obtain ⟨e', he', -⟩ := hctx.2 e s1
        rw [he'] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp [CoreOpsTry_traitFromResidualResult.from_residual,
          FromSame.from] at hok
    · obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      exact absurd hok (ctx_err_not_ok hks _ _ _)
  · split at hok
    · rename_i _ hdm
      split at hok
      · rename_i hq
        obtain ⟨r, hr, hok⟩ := bind_ok_inv hok
        obtain ⟨_, _, hok⟩ := bind_ok_inv hok
        obtain ⟨s1, _, hok⟩ := bind_ok_inv hok
        obtain ⟨r1, hr1, hok⟩ := bind_ok_inv hok
        obtain ⟨cf, hcf, hok⟩ := bind_ok_inv hok
        rcases r with ctx | e
        · rw [hctx.1] at hr1
          obtain rfl := ok_inj hr1
          simp [CoreOpsTry.branch] at hcf
          obtain rfl := hcf
          simp only at hok
          obtain ⟨c, hc, hok⟩ := bind_ok_inv hok
          exact ⟨ctx, c, hc, hok, Or.inl ⟨hdm, IScalar.val_eq_imp _ _ hq, hr⟩⟩
        · obtain ⟨e', he', -⟩ := hctx.2 e s1
          rw [he'] at hr1
          obtain rfl := ok_inj hr1
          simp [CoreOpsTry.branch] at hcf
          obtain rfl := hcf
          simp [CoreOpsTry_traitFromResidualResult.from_residual,
            FromSame.from] at hok
      · obtain ⟨_, _, hok⟩ := bind_ok_inv hok
        exact absurd hok (ctx_err_not_ok hselStr _ _ _)
    · rename_i _ hdm
      obtain ⟨r, hr, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨s1, _, hok⟩ := bind_ok_inv hok
      obtain ⟨r1, hr1, hok⟩ := bind_ok_inv hok
      obtain ⟨cf, hcf, hok⟩ := bind_ok_inv hok
      rcases r with ctx | e
      · rw [hctx.1] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp only at hok
        obtain ⟨c, hc, hok⟩ := bind_ok_inv hok
        exact ⟨ctx, c, hc, hok, Or.inr (Or.inl ⟨hdm, hr⟩)⟩
      · obtain ⟨e', he', -⟩ := hctx.2 e s1
        rw [he'] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp [CoreOpsTry_traitFromResidualResult.from_residual,
          FromSame.from] at hok
    · rename_i _ hdm
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      exact absurd hok (ctx_err_not_ok hselString _ _ _)
    · rename_i _ hdm
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      exact absurd hok (ctx_err_not_ok hks _ _ _)
    · rename_i _ hdm
      obtain ⟨r, hr, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨s1, _, hok⟩ := bind_ok_inv hok
      obtain ⟨r1, hr1, hok⟩ := bind_ok_inv hok
      obtain ⟨cf, hcf, hok⟩ := bind_ok_inv hok
      rcases r with ctx | e
      · rw [hctx.1] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp only at hok
        obtain ⟨c, hc, hok⟩ := bind_ok_inv hok
        obtain ⟨r2, hr2, hok⟩ := bind_ok_inv hok
        obtain ⟨cf1, hcf1, hok⟩ := bind_ok_inv hok
        rcases r2 with u | e2
        · cases u
          simp [CoreOpsTry.branch] at hcf1
          obtain rfl := hcf1
          simp only at hok
          exact ⟨ctx, c, hc, hok, Or.inr (Or.inr ⟨hdm, hr, hr2⟩)⟩
        · simp [CoreOpsTry.branch] at hcf1
          obtain rfl := hcf1
          simp [CoreOpsTry_traitFromResidualResult.from_residual,
            FromSame.from] at hok
      · obtain ⟨e', he', -⟩ := hctx.2 e s1
        rw [he'] at hr1
        obtain rfl := ok_inj hr1
        simp [CoreOpsTry.branch] at hcf
        obtain rfl := hcf
        simp [CoreOpsTry_traitFromResidualResult.from_residual,
          FromSame.from] at hok
    · obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      obtain ⟨_, _, hok⟩ := bind_ok_inv hok
      exact absurd hok (ctx_err_not_ok hks _ _ _)

end Keystore2Verify.Permission
