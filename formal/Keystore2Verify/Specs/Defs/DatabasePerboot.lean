import Keystore2Verify.Specs.Defs.Externals
import Keystore2Verify.Specs.Defs.ExternalsMore

/-!
# Definitions for the statements about `database/perboot.rs`

The per-boot database keeps its auth tokens in a `HashSet` behind a `RwLock`. The translation
leaves both opaque, so the statements only follow the values that the opaque calls return. This
file holds the assumption about the equality of two authenticator types, and an abbreviation of
the shared assumption about the clone of an auth token. Nothing here is an axiom.
-/

namespace Keystore2Verify.DatabasePerboot
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open HardwareAuthenticatorType.HardwareAuthenticatorType.Insts
open CoreCmpPartialEqHardwareAuthenticatorType renaming eq → hatyEq
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone renaming clone → hatClone
open database.perboot

/-- Assumption about an external function, over the function `eq`: `eq a b` never panics, and it
returns `true` exactly when `a = b`. -/
def HardwareAuthenticatorTypeEqAssumption
    (eq : HardwareAuthenticatorType.HardwareAuthenticatorType →
      HardwareAuthenticatorType.HardwareAuthenticatorType → Result Bool) : Prop :=
  ∀ a b, ∃ r, eq a b = ok r ∧ (r = true ↔ a = b)

/-- Assumption about an external function: the equality of two `HardwareAuthenticatorType`
values (register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-hardwareauthenticatortype-hardwareauthenticatortype-insts-corecmppartialeqhardwareauthenticatortype-eq`).
It is `HardwareAuthenticatorTypeEqAssumption` at the extracted symbol. Source: the AIDL stand-in
derives `PartialEq` for this enum. -/
def HardwareAuthenticatorTypeEqSpec : Prop :=
  HardwareAuthenticatorTypeEqAssumption hatyEq

/-- Assumption about an external function, over the function `clone`: `clone t` never panics and
returns a value equal to `t`. -/
def HardwareAuthTokenCloneAssumption
    (clone : HardwareAuthToken.HardwareAuthToken →
      Result HardwareAuthToken.HardwareAuthToken) : Prop :=
  ∀ t, clone t = ok t

/-- The clone of a `HardwareAuthToken` never panics and returns an equal token: the shared
assumption about this external function, `ExternalsMore.HardwareAuthTokenCloneSpec`. -/
abbrev HardwareAuthTokenCloneSpec : Prop := ExternalsMore.HardwareAuthTokenCloneSpec

/-- The number of a secure user id as a signed 64 bit integer. -/
abbrev idNum (x : utils.SecureUserId) : Int := (x : Std.I64).val

/-- The `AuthTokenId` that `from_auth_token` builds from a token: the user id, the authenticator
id and the authenticator type. -/
def idOf (t : HardwareAuthToken.HardwareAuthToken) : AuthTokenId :=
  { user_id := t.userId, auth_id := t.authenticatorId, authenticator_type := t.authenticatorType }

end Keystore2Verify.DatabasePerboot
