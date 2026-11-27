import Keystore2Verify.Specs.Defs.DatabasePerboot

namespace Keystore2Verify.DatabasePerboot
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open database.perboot
open AuthTokenEntryWrap.Insts
open CoreCloneClone renaming clone → wrapClone
open CoreHashHash renaming hash → wrapHash
open CoreCmpPartialEqAuthTokenEntryWrap renaming eq → wrapEq
open AuthTokenId.Insts.CoreHashHash renaming hash → idHash
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone renaming clone → hatClone
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts
open CoreCmpPartialEqHardwareAuthenticatorType renaming eq → hatyEq

/-- conditional: if cloning the token returns `hat`, `clone` returns the entry with that token and
the same `time_received`. Hypothesis: the call `HardwareAuthToken::clone` on `self.auth_token`
returns `ok hat`. -/
theorem auth_token_entry_wrap_clone_ok (self : AuthTokenEntryWrap)
    (hat : HardwareAuthToken.HardwareAuthToken)
    (h : hatClone self.auth_token
      = ok hat) :
    wrapClone self
      = ok { auth_token := hat, time_received := self.time_received } := by
  sorry

/-- conditional: if cloning the token fails with `e`, `clone` fails with `e`. Hypothesis: the call
`HardwareAuthToken::clone` on `self.auth_token` returns `fail e`. -/
theorem auth_token_entry_wrap_clone_fail (self : AuthTokenEntryWrap) (e : Error)
    (h : hatClone self.auth_token
      = fail e) :
    wrapClone self = fail e := by
  sorry

/-- conditional: `clone` returns an entry equal to `self`. Hypothesis:
`HardwareAuthTokenCloneSpec`. -/
theorem auth_token_entry_wrap_clone (hC : HardwareAuthTokenCloneSpec)
    (self : AuthTokenEntryWrap) :
    wrapClone self = ok self := by
  sorry

/-- exact: `hash` feeds the `AuthTokenId` of the token into the hasher and returns what that hash
returns (`ok` or `fail`). The `time_received` field and the fields of the token other than the
three that make the id take no part. -/
theorem auth_token_entry_wrap_hash {H : Type} (inst : core.hash.Hasher H)
    (self : AuthTokenEntryWrap) (state : H) :
    wrapHash inst self state
      = idHash inst (idOf self.auth_token) state := by
  sorry

/-- exact: if the `user_id`s or the `auth_id`s of the two tokens differ, `eq` returns `false`.
The `time_received` fields take no part. -/
theorem auth_token_entry_wrap_eq_ids_differ (a b : AuthTokenEntryWrap)
    (h : a.auth_token.userId ≠ b.auth_token.userId ∨
      a.auth_token.authenticatorId ≠ b.auth_token.authenticatorId) :
    wrapEq a b = ok false := by
  sorry

/-- exact: if the `user_id`s and the `auth_id`s are equal, `eq` returns what the equality of the
two authenticator types returns (`ok` or `fail`). -/
theorem auth_token_entry_wrap_eq_same_ids (a b : AuthTokenEntryWrap)
    (h1 : a.auth_token.userId = b.auth_token.userId)
    (h2 : a.auth_token.authenticatorId = b.auth_token.authenticatorId) :
    wrapEq a b
      = hatyEq a.auth_token.authenticatorType b.auth_token.authenticatorType := by
  sorry

/-- conditional: `eq` never fails and is `true` exactly when the three identifying fields of the
two tokens are equal. Hypothesis: `HardwareAuthenticatorTypeEqSpec`. -/
theorem auth_token_entry_wrap_eq (hEq : HardwareAuthenticatorTypeEqSpec)
    (a b : AuthTokenEntryWrap) :
    ∃ r, wrapEq a b = ok r ∧
      (r = true ↔ idOf a.auth_token = idOf b.auth_token) := by
  sorry

end Keystore2Verify.DatabasePerboot
