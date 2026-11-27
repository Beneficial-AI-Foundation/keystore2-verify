import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.thread.local
open Keystore2Verify.Externals
open enforcements.AuthInfo.after_finish.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared1RefCellKeystoreDBResultTupleError → afterFinishOnce

/-- exact: if the key has no usage limit, `after_finish` returns `Ok ()`. In the Rust source this
path does not touch the database. -/
theorem auth_info_after_finish_unlimited (self : enforcements.AuthInfo)
    (h : self.key_usage_limited = none) :
    enforcements.AuthInfo.after_finish self = ok (.Ok ()) := by
  sorry

/-- conditional: if the key has the usage limit `some key_id`, and `LocalKey::with` returns `Ok` for
the closure that updates the use counter, `after_finish` returns `Ok ()`. The statement does not say
that `with` runs the closure, so the closure body (`borrow_mut`, `check_and_update_key_usage_count`
and its `context`) is reached by no statement: `LocalKey::with` is an external function with no
assumption. Hypotheses: the outcomes of `globals::DB` (it returns `lk`) and of `LocalKey::with` on
`lk` and `key_id` (it returns `Ok`); the shared assumptions about `from_str_nonconst` and `format`;
and the `context` assumption at the outer call, which keeps an `Ok`. -/
theorem auth_info_after_finish_updated (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyCtxLaw root Unit)
    (self : enforcements.AuthInfo) (key_id : Std.I64)
    (lk : LocalKey (core.cell.RefCell database.KeystoreDB))
    (h : self.key_usage_limited = some key_id) (hdb : globals.DB = ok lk)
    (hwith : LocalKey.with afterFinishOnce lk key_id = ok (.Ok ())) :
    enforcements.AuthInfo.after_finish self = ok (.Ok ()) := by
  sorry

/-- conditional: if the key has the usage limit `some key_id`, and `LocalKey::with` returns the
error `e` for that closure, `after_finish` returns an error with the same root cause as `e`.
Hypotheses: those of `auth_info_after_finish_updated`, with the outcome of `LocalKey::with` being
`Err e`. -/
theorem auth_info_after_finish_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AnyCtxLaw root Unit)
    (self : enforcements.AuthInfo) (key_id : Std.I64)
    (lk : LocalKey (core.cell.RefCell database.KeystoreDB))
    (e : anyhow.Error)
    (h : self.key_usage_limited = some key_id) (hdb : globals.DB = ok lk)
    (hwith : LocalKey.with afterFinishOnce lk key_id = ok (.Err e)) :
    ∃ e', enforcements.AuthInfo.after_finish self = ok (.Err e') ∧ root e' = root e := by
  sorry
