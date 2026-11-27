import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.sync.poison
open std.sync.mpsc
open Keystore2Verify.Externals
open std.sync.poison.mutex
open MutexGuard.Insts
open CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut
open CoreOpsDerefDeref renaming deref → guardDeref
open android_hardware_security_keymint.aidl.android.hardware.security.keymint.ErrorCode.ErrorCode
  renaming KEY_USER_NOT_AUTHENTICATED → keyUserNotAuthenticated

/-! Common to all theorems about `AuthRequest::get_auth_tokens`: the call takes the token out of the
slot `self.hat` under its lock. The write-back of `take` is dropped by the translation, so no
statement says that the slot is empty afterwards. In the Rust source the constant
`ErrorCode::KEY_USER_NOT_AUTHENTICATED` and the first message are evaluated on every path that
passes the lock, also when the slot holds a token, so every path outside the panic needs their
hypotheses. -/

/-- conditional: if locking the token slot returns a poison error, the function panics (`fail`).
In the Rust source this path panics before the slot is read. Hypothesis: the outcome of
`Mutex::lock` on `self.hat`. -/
theorem auth_request_get_auth_tokens_slot_poisoned (self : enforcements.AuthRequest)
    (pe : PoisonError (MutexGuard (Option AuthToken)))
    (hlock : Mutex.lock self.hat = ok (.Err pe)) :
    enforcements.AuthRequest.get_auth_tokens self = fail Error.panic := by
  sorry

/-- conditional: if the token slot is empty, the function returns an error whose root cause is
`Error::Km(KEY_USER_NOT_AUTHENTICATED)`, whatever the state of the request. Hypotheses: the outcomes
of the lock `Mutex::lock` on `self.hat` (it returns the guard `g`), of `deref_mut` on `g` (it
returns the content `none`), and of the constant `KEY_USER_NOT_AUTHENTICATED` (it is `ec`); the
shared assumptions about `from_str_nonconst` and `format`; and the `context` assumption at the call
that adds the message to a keystore2 error. -/
theorem auth_request_get_auth_tokens_no_token (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken)
    (self : enforcements.AuthRequest) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (none, f))
    (hec : keyUserNotAuthenticated = ok ec) :
    ∃ e, enforcements.AuthRequest.get_auth_tokens self = ok (.Err e) ∧
      root e = ErrRoot.ks (error.Error.Km ec) := by
  sorry

/-- conditional: for a request in the state `OpAuth` whose slot holds the token `hat`, the function
returns `Ok (hat, None)`. Hypotheses: the outcomes of `Mutex::lock` (the guard `g`), of `deref_mut`
on `g` (the content `some hat`) and of the constant `KEY_USER_NOT_AUTHENTICATED` (`ec`, which Rust
evaluates also when the slot holds a token); the shared assumptions about `from_str_nonconst` and
`format`; and the `context` assumption at the call that adds the message, which keeps an `Ok`. -/
theorem auth_request_get_auth_tokens_op_auth (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (hstate : self.state = enforcements.AuthRequestState.OpAuth)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec) :
    enforcements.AuthRequest.get_auth_tokens self = ok (.Ok (hat, none)) := by
  sorry

/-- conditional: for a request in the state `TimeStamp recv` whose slot holds the token `hat`, if
locking `recv` returns a poison error, the function panics (`fail`). In the Rust source this path
panics before the receiver is read. Hypotheses: the outcomes of `Mutex::lock` on `self.hat` (the
guard `g`), of `deref_mut` on `g` (the content `some hat`), of the constant
`KEY_USER_NOT_AUTHENTICATED` (`ec`) and of `Mutex::lock` on `recv`; the shared assumptions about
`from_str_nonconst` and `format`; and the `context` assumption of the first message. -/
theorem auth_request_get_auth_tokens_timestamp_poisoned (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (pe : PoisonError
      (MutexGuard (TsReceiver)))
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec) (hlock1 : Mutex.lock recv = ok (.Err pe)) :
    enforcements.AuthRequest.get_auth_tokens self = fail Error.panic := by
  sorry

/-- conditional: for a request in the state `TimeStamp recv` whose slot holds the token `hat`, if
the receive on `recv` returns the timestamp token `tst`, the function returns `Ok (hat, Some tst)`.
Hypotheses: the outcomes of `Mutex::lock` on `self.hat` (the guard `g`), of `deref_mut` on `g` (the
content `some hat`), of the constant `KEY_USER_NOT_AUTHENTICATED` (`ec`), of `Mutex::lock` on `recv`
(the guard `g1`), of `deref` on `g1` (the receiver `r`) and of `Receiver::recv` on `r`; the shared
assumptions about `from_str_nonconst` and `format`; and the `context` assumptions of the three
messages (`KsStringCtxAssumption` twice, `RecvStrCtxAssumption` once), which keep an `Ok`. -/
theorem auth_request_get_auth_tokens_timestamp_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken) (hctx1 : RecvStrCtxAssumption root)
    (hctx2 : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (g1 : MutexGuard (TsReceiver))
    (r : TsReceiver) (tst : TimeStamp)
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec)
    (hlock1 : Mutex.lock recv = ok (.Ok g1)) (hderef : guardDeref g1 = ok r)
    (hrecv : Receiver.recv r = ok (.Ok (.Ok tst))) :
    enforcements.AuthRequest.get_auth_tokens self = ok (.Ok (hat, some tst)) := by
  sorry

/-- conditional: for a request in the state `TimeStamp recv` whose slot holds the token `hat`, if
the receive on `recv` returns the error `e` that the worker sent, the function returns an error
whose root cause is `e`. Hypotheses: those of `auth_request_get_auth_tokens_timestamp_ok`, with
the outcome of `Receiver::recv` on `r` being `Ok (Err e)`. -/
theorem auth_request_get_auth_tokens_timestamp_worker_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken) (hctx1 : RecvStrCtxAssumption root)
    (hctx2 : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (g1 : MutexGuard (TsReceiver))
    (r : TsReceiver) (e : error.Error)
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec)
    (hlock1 : Mutex.lock recv = ok (.Ok g1)) (hderef : guardDeref g1 = ok r)
    (hrecv : Receiver.recv r = ok (.Ok (.Err e))) :
    ∃ e', enforcements.AuthRequest.get_auth_tokens self = ok (.Err e') ∧
      root e' = ErrRoot.ks e := by
  sorry

/-- conditional: for a request in the state `TimeStamp recv` whose slot holds the token `hat`, if
the receive on `recv` returns a `RecvError` (the sender is gone), the function returns an error
whose root cause is that `RecvError`. `ErrRoot` has no constructor for it, so the class is `other`.
Hypotheses: those of `auth_request_get_auth_tokens_timestamp_ok`, without the worker-result context
assumption, and with the outcome of `Receiver::recv` on `r` being `Err re`. In the Rust source this
path returns before the second message is formatted. -/
theorem auth_request_get_auth_tokens_timestamp_disconnected (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root AuthToken) (hctx1 : RecvStrCtxAssumption root)
    (self : enforcements.AuthRequest) (hat : AuthToken) (g : MutexGuard (Option AuthToken))
    (f : Option AuthToken → MutexGuard (Option AuthToken))
    (ec : KmErrorCode)
    (recv : Mutex (TsReceiver))
    (g1 : MutexGuard (TsReceiver))
    (r : TsReceiver)
    (re : RecvError)
    (hstate : self.state = enforcements.AuthRequestState.TimeStamp recv)
    (hlock : Mutex.lock self.hat = ok (.Ok g)) (hmut : guardDerefMut g = ok (some hat, f))
    (hec : keyUserNotAuthenticated = ok ec)
    (hlock1 : Mutex.lock recv = ok (.Ok g1)) (hderef : guardDeref g1 = ok r)
    (hrecv : Receiver.recv r = ok (.Err re)) :
    ∃ e', enforcements.AuthRequest.get_auth_tokens self = ok (.Err e') ∧
      root e' = ErrRoot.other := by
  sorry
