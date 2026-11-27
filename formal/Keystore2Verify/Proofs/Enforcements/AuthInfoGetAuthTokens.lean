import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint.ErrorCode.ErrorCode
  renaming KEY_USER_NOT_AUTHENTICATED → keyUserNotAuthenticated
open enforcements.DeferredAuthState

/-- exact: if no authorization is required, `get_auth_tokens` returns `Ok (None, None)` and leaves
the auth info unchanged. -/
theorem auth_info_get_auth_tokens_no_auth (self : enforcements.AuthInfo)
    (h : self.state = NoAuthRequired) :
    enforcements.AuthInfo.get_auth_tokens self = ok (.Ok (none, none), self) := by
  sorry

/-- conditional: if the auth info already holds the tokens `hat` and `tst`, `get_auth_tokens`
returns them (`Some hat` and `tst`) and leaves the auth info unchanged. Hypotheses: the
assumptions about `clone` of an auth token and of an optional timestamp token. -/
theorem auth_info_get_auth_tokens_token (hc : AuthTokenCloneSpec)
    (hc1 : OptionTimeStampCloneSpec)
    (self : enforcements.AuthInfo) (hat : AuthToken) (tst : Option TimeStamp)
    (h : self.state = Token hat tst) :
    enforcements.AuthInfo.get_auth_tokens self = ok (.Ok (some hat, tst), self) := by
  sorry

/-- conditional: if the operation waits for a per-operation token, `get_auth_tokens` returns the
tokens that the request holds: `Some hat` and `tst`, and the new auth info holds them in the state
`Token hat tst`. The returned tokens are clones; the stored ones are the originals. Hypotheses: the
outcome of `deref` on the `Arc` of the request (it returns `ar`); the outcome of
`AuthRequest::get_auth_tokens` on `ar` (it returns `Ok (hat, tst)`); the `context` assumption at the
call that adds the message, which keeps an `Ok`; and the assumptions about `clone`. -/
theorem auth_info_get_auth_tokens_waiting_ok (root : anyhow.Error → ErrRoot)
    (hctx : Permission.AnyhowStrCtxLaw root (AuthToken × Option TimeStamp))
    (hc : AuthTokenCloneSpec) (hc1 : OptionTimeStampCloneSpec)
    (self : enforcements.AuthInfo) (req : alloc.sync.Arc enforcements.AuthRequest)
    (ar : enforcements.AuthRequest) (hat : AuthToken) (tst : Option TimeStamp)
    (h : self.state = Waiting req)
    (hderef : arcDeref alloc.alloc.Global req = ok ar)
    (hget : enforcements.AuthRequest.get_auth_tokens ar = ok (.Ok (hat, tst))) :
    enforcements.AuthInfo.get_auth_tokens self
      = ok (.Ok (some hat, tst), { self with state := Token hat tst }) := by
  sorry

/-- conditional: if the operation waits for a per-operation token and the request returns the error
`e`, `get_auth_tokens` returns an error with the same root cause as `e`, and leaves the auth info
unchanged (it stays in the state `Waiting`). Hypotheses: the outcome of `deref` on the `Arc` of the
request (it returns `ar`); the outcome of `AuthRequest::get_auth_tokens` on `ar` (it returns
`Err e`); and the `context` assumption at the call that adds the message. -/
theorem auth_info_get_auth_tokens_waiting_err (root : anyhow.Error → ErrRoot)
    (hctx : Permission.AnyhowStrCtxLaw root (AuthToken × Option TimeStamp))
    (self : enforcements.AuthInfo) (req : alloc.sync.Arc enforcements.AuthRequest)
    (ar : enforcements.AuthRequest) (e : anyhow.Error)
    (h : self.state = Waiting req)
    (hderef : arcDeref alloc.alloc.Global req = ok ar)
    (hget : enforcements.AuthRequest.get_auth_tokens ar = ok (.Err e)) :
    ∃ e', enforcements.AuthInfo.get_auth_tokens self = ok (.Err e', self) ∧
      root e' = root e := by
  sorry

/-- conditional: if the operation needs a per-operation token that was never requested
(`OpAuthRequired`), `get_auth_tokens` returns an error whose root cause is
`Error::Km(KEY_USER_NOT_AUTHENTICATED)`, and leaves the auth info unchanged. Hypotheses: the outcome
of the constant `KEY_USER_NOT_AUTHENTICATED` (it is `ec`); the shared assumptions about
`from_str_nonconst` and `format`; and the `context` assumption at the call that adds the message to
a keystore2 error. -/
theorem auth_info_get_auth_tokens_op_auth_required (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root (Option AuthToken × Option TimeStamp))
    (self : enforcements.AuthInfo) (sids : alloc.vec.Vec utils.SecureUserId)
    (ty : AuthType)
    (ec : KmErrorCode)
    (h : self.state = OpAuthRequired sids ty) (hec : keyUserNotAuthenticated = ok ec) :
    ∃ e, enforcements.AuthInfo.get_auth_tokens self = ok (.Err e, self) ∧
      root e = ErrRoot.ks (error.Error.Km ec) := by
  sorry

/-- conditional: if the operation needs a timestamp token that was never requested
(`TimeStampRequired`), `get_auth_tokens` returns an error whose root cause is
`Error::Km(KEY_USER_NOT_AUTHENTICATED)`, and leaves the auth info unchanged. Hypotheses: those of
`auth_info_get_auth_tokens_op_auth_required`. -/
theorem auth_info_get_auth_tokens_timestamp_required (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root (Option AuthToken × Option TimeStamp))
    (self : enforcements.AuthInfo) (hat : AuthToken)
    (ec : KmErrorCode)
    (h : self.state = TimeStampRequired hat) (hec : keyUserNotAuthenticated = ok ec) :
    ∃ e, enforcements.AuthInfo.get_auth_tokens self = ok (.Err e, self) ∧
      root e = ErrRoot.ks (error.Error.Km ec) := by
  sorry
