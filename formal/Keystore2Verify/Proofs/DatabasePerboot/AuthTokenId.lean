import Keystore2Verify.Specs.Defs.DatabasePerboot

namespace Keystore2Verify.DatabasePerboot
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open database.perboot
open AuthTokenId.Insts
open CoreCmpPartialEqAuthTokenId renaming eq → idEq
open CoreCmpOrd renaming cmp → idCmp
open CoreCmpPartialOrdAuthTokenId renaming partial_cmp → idPartialCmp
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts
open CoreCmpPartialEqHardwareAuthenticatorType renaming eq → hatyEq
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts.CoreCmpOrd renaming cmp → hatyCmp

/-- exact: when the `user_id`s differ, `eq` returns `false`. In the Rust source the other fields
are not compared on this path. -/
theorem auth_token_id_eq_user_id_differs (a b : AuthTokenId) (h : a.user_id ≠ b.user_id) :
    idEq a b = ok false := by
  sorry

/-- exact: when the `user_id`s are equal and the `auth_id`s differ, `eq` returns `false`. In the
Rust source `authenticator_type` is not compared on this path. -/
theorem auth_token_id_eq_auth_id_differs (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id ≠ b.auth_id) :
    idEq a b = ok false := by
  sorry

/-- exact: when `user_id` and `auth_id` are equal, `eq` returns what the equality of the two
`authenticator_type` values returns (`ok` or `fail`). -/
theorem auth_token_id_eq_same_ids (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id = b.auth_id) :
    idEq a b
      = hatyEq a.authenticator_type b.authenticator_type := by
  sorry

/-- conditional: `eq` never fails and is `true` exactly when the three fields are equal.
Hypothesis: `HardwareAuthenticatorTypeEqSpec`. -/
theorem auth_token_id_eq (hEq : HardwareAuthenticatorTypeEqSpec) (a b : AuthTokenId) :
    ∃ r, idEq a b = ok r ∧
      (r = true ↔ a = b) := by
  sorry

/-- exact: when the `user_id`s differ, `cmp` returns the signed order of the two numbers. -/
theorem auth_token_id_cmp_user_id_differs (a b : AuthTokenId) (h : a.user_id ≠ b.user_id) :
    idCmp a b = ok (compare (idNum a.user_id) (idNum b.user_id)) := by
  sorry

/-- exact: when the `user_id`s are equal and the `auth_id`s differ, `cmp` returns the signed
order of the two `auth_id` numbers. -/
theorem auth_token_id_cmp_auth_id_differs (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id ≠ b.auth_id) :
    idCmp a b = ok (compare (idNum a.auth_id) (idNum b.auth_id)) := by
  sorry

/-- exact: when `user_id` and `auth_id` are equal, `cmp` returns what the `cmp` of the two
`authenticator_type` values returns (`ok` or `fail`). -/
theorem auth_token_id_cmp_same_ids (a b : AuthTokenId) (h1 : a.user_id = b.user_id)
    (h2 : a.auth_id = b.auth_id) :
    idCmp a b = hatyCmp a.authenticator_type b.authenticator_type := by
  sorry

/-- exact: if `cmp` returns `ok o`, then `partial_cmp` returns `ok (some o)`. -/
theorem auth_token_id_partial_cmp_ok (a b : AuthTokenId) (o : Ordering)
    (h : idCmp a b = ok o) :
    idPartialCmp a b = ok (some o) := by
  sorry

/-- exact: if `cmp` fails with `e`, then `partial_cmp` fails with `e`. -/
theorem auth_token_id_partial_cmp_fail (a b : AuthTokenId) (e : Error)
    (h : idCmp a b = fail e) :
    idPartialCmp a b = fail e := by
  sorry

/-- exact: `from_auth_token` never fails. It copies `userId`, `authenticatorId` and
`authenticatorType` of the token. The other fields of the token are not used. -/
theorem auth_token_id_from_auth_token (tok : HardwareAuthToken.HardwareAuthToken) :
    AuthTokenId.from_auth_token tok = ok
      { user_id := tok.userId, auth_id := tok.authenticatorId,
        authenticator_type := tok.authenticatorType } := by
  sorry

end Keystore2Verify.DatabasePerboot
