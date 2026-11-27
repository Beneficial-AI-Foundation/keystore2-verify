import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.Maintenance
open Aeneas Aeneas.Std Result keystore2
open std.thread.local.LocalKey renaming «with» → localLocalKeywith
open Keystore2Verify.Externals
open maintenance.Maintenance renaming get_app_uids_affected_by_sid → getAppUids
open maintenance.Maintenance.get_app_uids_affected_by_sid.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleShared2RefCellKeystoreDBResultVecAppUidError → uidsClosure

/-- conditional: if the permission check `MANAGE_USERS` returns an error `e`,
`get_app_uids_affected_by_sid` returns an error with the same root cause. In the Rust source the
database is not touched on this path. Hypotheses: the outcome of the permission check (an item of
keystore2 that the extraction could not translate, and a binder call); `format` and
`from_str_nonconst` do not fail; the assumption about `context` for an `anyhow::Error`
(`AnyCtxLaw`). -/
theorem get_app_uids_affected_by_sid_denied (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root Unit)
    (user : utils.AndroidUserId) (sid : utils.SecureUserId) (e : anyhow.Error)
    (hperm : utils.check_get_app_uids_affected_by_sid_permissions = ok (.Err e)) :
    ∃ e', getAppUids user sid = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the permission check passes and the closure on the thread-local database
returns `Ok uids`, `get_app_uids_affected_by_sid` returns `Ok uids`. Hypotheses: the outcomes of
the permission check, of `DB`, and of `LocalKey::with` (which borrows the database cell and
queries the database for `user` and `sid`); `format` and `from_str_nonconst` do not fail; the
assumptions about `context` for an `anyhow::Error` (`AnyCtxLaw`). The database that the query
returns is dropped, so no change to it is visible. -/
theorem get_app_uids_affected_by_sid_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root Unit) (hany2 : AnyCtxLaw root (alloc.vec.Vec utils.AppUid))
    (user : utils.AndroidUserId) (sid : utils.SecureUserId)
    (hperm : utils.check_get_app_uids_affected_by_sid_permissions = ok (.Ok ()))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (uids : alloc.vec.Vec utils.AppUid)
    (hwith : localLocalKeywith uidsClosure lk (user, sid) = ok (.Ok uids)) :
    getAppUids user sid = ok (.Ok uids) := by
  sorry

/-- conditional: if the permission check passes and the closure on the thread-local database returns
an error `e`, `get_app_uids_affected_by_sid` returns an error with the same root cause.
Hypotheses: the outcomes of the permission check, of `DB`, and of `LocalKey::with`; `format` and
`from_str_nonconst` do not fail; the assumptions about `context` for an `anyhow::Error`
(`AnyCtxLaw`). -/
theorem get_app_uids_affected_by_sid_db_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root Unit) (hany2 : AnyCtxLaw root (alloc.vec.Vec utils.AppUid))
    (user : utils.AndroidUserId) (sid : utils.SecureUserId)
    (hperm : utils.check_get_app_uids_affected_by_sid_permissions = ok (.Ok ()))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (e : anyhow.Error)
    (hwith : localLocalKeywith uidsClosure lk (user, sid) = ok (.Err e)) :
    ∃ e', getAppUids user sid = ok (.Err e') ∧ root e' = root e := by
  sorry
