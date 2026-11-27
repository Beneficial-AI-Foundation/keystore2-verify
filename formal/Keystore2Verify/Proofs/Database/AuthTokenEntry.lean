import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open database.AuthTokenEntry.Insts.CoreCloneClone renaming clone → authTokenEntryClone
open database.AuthTokenEntry.satisfies.closure.Insts
  renaming CoreOpsFunctionFnMutTupleShared0SecureUserIdBool → satisfiesFnMut
open database.AuthTokenEntry renaming satisfies → authTokenEntrySatisfies
open database.AuthTokenEntry.impl renaming auth_token → authTokenEntryAuthToken
open database.AuthTokenEntry renaming take_auth_token → authTokenEntryTakeAuthToken
open database.AuthTokenEntry.impl renaming time_received → authTokenEntryTimeReceived
open database.AuthTokenEntry renaming challenge → authTokenEntryChallenge

/-- conditional: `clone` never fails and returns an equal entry. Hypothesis:
`HardwareAuthTokenCloneSpec` (the `BootTime` clone is a copy). -/
theorem auth_token_entry_clone (h : HardwareAuthTokenCloneSpec)
    (e : database.AuthTokenEntry) : authTokenEntryClone e = ok e := by
  sorry

/-- conditional: `satisfies` never fails. It returns `true` exactly when some user id `sid` of the
list equals the `userId` or the `authenticatorId` of the token, and the bitwise `and` of
`auth_type` and the `authenticatorType` of the token is not zero. The empty list gives `false`.
Hypothesis: `IterAnySpec` for the closure (assumption about `Iter::any`). -/
theorem auth_token_entry_satisfies
    (h : IterAnySpec satisfiesFnMut)
    (e : database.AuthTokenEntry) (sids : Slice utils.SecureUserId)
    (t : HardwareAuthenticatorType.HardwareAuthenticatorType) :
    ∃ b, authTokenEntrySatisfies e sids t = ok b ∧
      (b = true ↔ ∃ sid ∈ sids.val,
        (sid = e.auth_token.userId ∨ sid = e.auth_token.authenticatorId) ∧
        (t &&& e.auth_token.authenticatorType) ≠ 0#i32) := by
  sorry

/-- exact: `auth_token` never fails and returns the token. -/
theorem auth_token_entry_auth_token (e : database.AuthTokenEntry) :
    authTokenEntryAuthToken e = ok e.auth_token := by
  sorry

/-- exact: `take_auth_token` never fails and returns the token. -/
theorem auth_token_entry_take_auth_token (e : database.AuthTokenEntry) :
    authTokenEntryTakeAuthToken e = ok e.auth_token := by
  sorry

/-- exact: `time_received` never fails and returns the time at which the token was received. -/
theorem auth_token_entry_time_received (e : database.AuthTokenEntry) :
    authTokenEntryTimeReceived e = ok e.time_received := by
  sorry

/-- exact: `challenge` never fails and returns the challenge of the token. -/
theorem auth_token_entry_challenge (e : database.AuthTokenEntry) :
    authTokenEntryChallenge e = ok e.auth_token.challenge := by
  sorry
