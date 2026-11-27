import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open enforcements.Enforcements.get_auth_tokens
open closure.Insts renaming CoreOpsFunctionFnTupleShared3AuthTokenEntryBool → byChallenge
open closure_1.Insts renaming CoreOpsFunctionFnTupleShared4AuthTokenEntryBool → byAge
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open HardwareAuthenticatorType.HardwareAuthenticatorType renaming ANY → authTypeAny
open android_security_authorization.aidl.android.security.authorization.ResponseCode.ResponseCode
  renaming NO_AUTH_TOKEN_FOUND → noAuthTokenFound

/-! `Enforcements::get_auth_tokens` makes at most two searches. The first looks for a token with the
given challenge and a matching `sid`: the call `find_auth_token` with the predicate `byChallenge`
on `(challenge, [sid], ANY)`. The second looks for a token younger than `auth_token_max_age_millis`
that matches `sid`: the predicate `byAge` on `(now, max_age, [sid], ANY)`, where `now` is
`BootTime::now()`. What a search returns lies in the per-boot database item, which the translation
leaves opaque, and nothing links the predicate to the result (blocked by extraction). So every
statement takes the result of a search as a hypothesis. When a search finds the entry `e`, the auth
token returned is the one in `e`. The parameter `self` is not used. -/

/-- conditional: if the search by challenge finds the entry `e`, and the timestamp token for
`challenge` is `tst`, `get_auth_tokens` returns `Ok (e.auth_token, tst)`. The maximum age is not
used. Hypotheses: the outcomes of the constant `HardwareAuthenticatorType::ANY` (it returns `any`),
of the search by challenge (`some e`) and of `get_timestamp_token` (`Ok tst`); the shared
assumptions about `from_str_nonconst` and `format`; and the `context` assumption at the call that
adds the message, which keeps an `Ok`. -/
theorem enforcements_get_auth_tokens_by_challenge (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (e : database.AuthTokenEntry) (tst : TimeStamp)
    (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Ok tst)) :
    enforcements.Enforcements.get_auth_tokens self challenge sid max_age
      = ok (.Ok (e.auth_token, tst)) := by
  sorry

/-- conditional: if the search by challenge finds an entry, and `get_timestamp_token` returns the
error `te`, `get_auth_tokens` returns an error whose root cause is `te`. Hypotheses: those of
`enforcements_get_auth_tokens_by_challenge`, with the outcome of `get_timestamp_token` being
`Err te`. -/
theorem enforcements_get_auth_tokens_by_challenge_clock_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (e : database.AuthTokenEntry) (te : error.Error)
    (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Err te)) :
    ∃ e', enforcements.Enforcements.get_auth_tokens self challenge sid max_age = ok (.Err e') ∧
      root e' = ErrRoot.ks te := by
  sorry

/-- conditional: if the search by challenge finds nothing and the maximum age is 0,
`get_auth_tokens` returns an error whose root cause is the `authorization::Error::Rc` of
`NO_AUTH_TOKEN_FOUND`. `ErrRoot` has no constructor for that type, so the class is `other`. In the
Rust source this path returns before the clock is read and before the second search. Hypotheses:
the outcomes of the constant `ANY` (it returns `any`), of the search by challenge (`none`) and of
the constant `NO_AUTH_TOKEN_FOUND`; the shared assumptions about `from_str_nonconst` and `format`;
and the `context` assumption at the call that adds the message to an authorization error. -/
theorem enforcements_get_auth_tokens_age_zero (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AuthzStringCtxAssumption root (AuthToken × TimeStamp))
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (rc : AuthzResponseCode)
    (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hrc : noAuthTokenFound = ok rc) :
    ∃ e, enforcements.Enforcements.get_auth_tokens self challenge sid 0#i64 = ok (.Err e) ∧
      root e = ErrRoot.other := by
  sorry

/-- conditional: if the search by challenge finds nothing, the maximum age is not 0, and the search
by age finds nothing, `get_auth_tokens` returns an error whose root cause is the
`authorization::Error::Rc` of `NO_AUTH_TOKEN_FOUND` (class `other`, as in
`enforcements_get_auth_tokens_age_zero`). In the Rust source the timestamp token is not requested.
Hypotheses: those of `enforcements_get_auth_tokens_age_zero` for the first search, `max_age` is not
0, `BootTime::now()` returns `now`, and the search by age is `none`. -/
theorem enforcements_get_auth_tokens_not_found (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : AuthzStringCtxAssumption root (AuthToken × TimeStamp))
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (now : database.BootTime)
    (rc : AuthzResponseCode)
    (hmax : max_age ≠ 0#i64) (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hnow : database.BootTime.now = ok now)
    (hfind1 : enforcements.Enforcements.find_auth_token byAge (now, max_age, sidVec sid, any)
      = ok none)
    (hrc : noAuthTokenFound = ok rc) :
    ∃ e, enforcements.Enforcements.get_auth_tokens self challenge sid max_age = ok (.Err e) ∧
      root e = ErrRoot.other := by
  sorry

/-- conditional: if the search by challenge finds nothing, the maximum age is not 0, and the search
by age finds the entry `e`, `get_auth_tokens` returns `Ok (e.auth_token, tst)`, where `tst` is the
timestamp token for `challenge`. Hypotheses: those of `enforcements_get_auth_tokens_not_found`,
without the `NO_AUTH_TOKEN_FOUND` constant outcome, except that the last search is `some e`; and the
outcome of `get_timestamp_token` (`Ok tst`); the `context` assumption of the timestamp message
replaces the one of the authorization error. -/
theorem enforcements_get_auth_tokens_by_age (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (now : database.BootTime) (e : database.AuthTokenEntry) (tst : TimeStamp)
    (hmax : max_age ≠ 0#i64) (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hnow : database.BootTime.now = ok now)
    (hfind1 : enforcements.Enforcements.find_auth_token byAge (now, max_age, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Ok tst)) :
    enforcements.Enforcements.get_auth_tokens self challenge sid max_age
      = ok (.Ok (e.auth_token, tst)) := by
  sorry

/-- conditional: if the search by challenge finds nothing, the maximum age is not 0, the search by
age finds an entry, and `get_timestamp_token` returns the error `te`, `get_auth_tokens` returns an
error whose root cause is `te`. Hypotheses: those of `enforcements_get_auth_tokens_by_age`, with the
outcome of `get_timestamp_token` being `Err te`. -/
theorem enforcements_get_auth_tokens_by_age_clock_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : KsStringCtxAssumption root TimeStamp)
    (self : enforcements.Enforcements) (challenge : utils.Challenge) (sid : utils.SecureUserId)
    (max_age : Std.I64) (any : HardwareAuthenticatorType.HardwareAuthenticatorType)
    (now : database.BootTime) (e : database.AuthTokenEntry) (te : error.Error)
    (hmax : max_age ≠ 0#i64) (hany : authTypeAny = ok any)
    (hfind : enforcements.Enforcements.find_auth_token byChallenge (challenge, sidVec sid, any)
      = ok none)
    (hnow : database.BootTime.now = ok now)
    (hfind1 : enforcements.Enforcements.find_auth_token byAge (now, max_age, sidVec sid, any)
      = ok (some e))
    (hts : enforcements.get_timestamp_token challenge = ok (.Err te)) :
    ∃ e', enforcements.Enforcements.get_auth_tokens self challenge sid max_age = ok (.Err e') ∧
      root e' = ErrRoot.ks te := by
  sorry
