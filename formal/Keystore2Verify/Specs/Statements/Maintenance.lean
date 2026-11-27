import Keystore2Verify.Proofs.Maintenance.GetAppUidsAffectedBySid

namespace Keystore2Verify.Maintenance

section GetAppUidsAffectedBySid
open Aeneas Aeneas.Std Result keystore2
open std.thread.local.LocalKey renaming «with» → localLocalKeywith
open Keystore2Verify.Externals
open maintenance.Maintenance renaming get_app_uids_affected_by_sid → getAppUids
open maintenance.Maintenance.get_app_uids_affected_by_sid.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleShared2RefCellKeystoreDBResultVecAppUidError → uidsClosure

recall get_app_uids_affected_by_sid_denied (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root Unit)
    (user : utils.AndroidUserId) (sid : utils.SecureUserId) (e : anyhow.Error)
    (hperm : utils.check_get_app_uids_affected_by_sid_permissions = ok (.Err e)) :
    ∃ e', getAppUids user sid = ok (.Err e') ∧ root e' = root e

recall get_app_uids_affected_by_sid_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root Unit) (hany2 : AnyCtxLaw root (alloc.vec.Vec utils.AppUid))
    (user : utils.AndroidUserId) (sid : utils.SecureUserId)
    (hperm : utils.check_get_app_uids_affected_by_sid_permissions = ok (.Ok ()))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (uids : alloc.vec.Vec utils.AppUid)
    (hwith : localLocalKeywith uidsClosure lk (user, sid) = ok (.Ok uids)) :
    getAppUids user sid = ok (.Ok uids)

recall get_app_uids_affected_by_sid_db_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root Unit) (hany2 : AnyCtxLaw root (alloc.vec.Vec utils.AppUid))
    (user : utils.AndroidUserId) (sid : utils.SecureUserId)
    (hperm : utils.check_get_app_uids_affected_by_sid_permissions = ok (.Ok ()))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (e : anyhow.Error)
    (hwith : localLocalKeywith uidsClosure lk (user, sid) = ok (.Err e)) :
    ∃ e', getAppUids user sid = ok (.Err e') ∧ root e' = root e

end GetAppUidsAffectedBySid

end Keystore2Verify.Maintenance
