import Keystore2Verify.Specs.Defs.Externals
import Keystore2Verify.Specs.Defs.ExternalsMore
import Keystore2Verify.Specs.Defs.Permission

/-!
# Definitions for the statements about `enforcements.rs`

The `context` assumptions at the call sites of the file, the assumptions about two external
functions (`clone` of an auth token, shared with other spec files, and of an optional timestamp
token), and the pure model of
`super_encryption_required`. Nothing here is an axiom.
-/

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay
open error.Error.Insts renaming CoreErrorError → KsErrorError
open anyhow.context.ext.StdError renaming Blanket → StdBlanket
open Keystore2Verify.Externals
open std.sync.mpsc
open std.sync.mpsc.RecvError.Insts renaming CoreErrorError → RecvErrorError
open authorization.Error.Insts renaming CoreErrorError → AuthzErrorError
open core.option.Option.Insts.CoreCloneClone renaming clone → optionClone
open alloc.slice.Slice renaming into_vec → sliceIntoVec
open std.hash.random
open core.borrow.Borrow renaming Blanket → borrowBlanket
open std.collections.hash.set
open utils.AndroidUserId
open std.hash.random.RandomState.Insts renaming CoreHashBuildHasherDefaultHasher → buildHasher

/-! ## Short names for the types of the file -/

open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open android_hardware_security_secureclock.aidl.android.hardware.security.secureclock
open android_security_authorization.aidl.android.security.authorization
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone renaming clone → authTokenClone
open TimeStampToken.TimeStampToken.Insts renaming CoreCloneClone → timeStampCloneInst

/-- The AIDL `HardwareAuthToken`. -/
abbrev AuthToken : Type := HardwareAuthToken.HardwareAuthToken

/-- The AIDL `TimeStampToken`. -/
abbrev TimeStamp : Type := TimeStampToken.TimeStampToken

/-- The AIDL `ErrorCode`. -/
abbrev KmErrorCode : Type := ErrorCode.ErrorCode

/-- The AIDL `HardwareAuthenticatorType`. -/
abbrev AuthType : Type := HardwareAuthenticatorType.HardwareAuthenticatorType

/-- The AIDL `ResponseCode` of the authorization service. -/
abbrev AuthzResponseCode : Type := ResponseCode.ResponseCode

/-- What a timestamp worker sends: a timestamp token or an error. -/
abbrev TsResult : Type := core.result.Result TimeStamp error.Error

/-- The receiving end of the channel of a timestamp worker. -/
abbrev TsReceiver : Type := Receiver TsResult

/-- The receiving end of the channel of confirmation tokens. -/
abbrev ByteReceiver : Type := Receiver (alloc.vec.Vec Std.U8)

/-! ## Context assumptions

Each assumption is the `context` assumption of `Externals.lean` at one kind of call: the error type
of the `Err` input, the type `T` of the `Ok` input and the type of the message. -/

open core.result.Result.Insts.AnyhowContext in
/-- A call `Err(keystore2_error).context(format!(..))` on a result that holds a `T`. The root cause
of the new error is the keystore2 error. -/
abbrev KsStringCtxAssumption (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun x => ErrRoot.ks x) root
    (context (T := T) (StdBlanket KsErrorError) StringDisplay)

open core.result.Result.Insts.AnyhowContext in
/-- A call `Err(authorization_error).context(format!(..))` on a result that holds a `T`. The class
of the root cause is `other`: `ErrRoot` (in `Externals.lean`) has no constructor for
`authorization::Error`, and none can be added here, so the class stays `other`. -/
abbrev AuthzStringCtxAssumption (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun _ => ErrRoot.other) root
    (context (T := T) (StdBlanket AuthzErrorError) StringDisplay)

open core.result.Result.Insts.AnyhowContext in
/-- The call `recv.recv().context("..")` on a result that holds a `Result<TimeStampToken, Error>`
or a `RecvError`. The class of the root cause of the new error is `other`: `ErrRoot` has no
constructor for `RecvError`. -/
abbrev RecvStrCtxAssumption (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw (fun _ => ErrRoot.other) root
    (context (T := TsResult)
      (StdBlanket RecvErrorError)
      (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay))

/-! ## Assumptions about external functions -/

/-- Assumption about an external function `clone`: it never panics and returns an equal value.
Idealisation: allocation never fails. -/
def CloneIdAssumption {T : Type} (clone : T → Result T) : Prop :=
  ∀ x, clone x = ok x

/-- The clone of a `HardwareAuthToken` never panics and returns an equal token: the shared
assumption about this external function, `ExternalsMore.HardwareAuthTokenCloneSpec`. -/
abbrev AuthTokenCloneSpec : Prop := ExternalsMore.HardwareAuthTokenCloneSpec

/-- Assumption about an external function (register record
`ks2-ext-core-option-option-insts-corecloneclone-clone`).
`Option<TimeStampToken>::clone` returns an equal value and does not panic. The element type is a
plain data struct whose derived `Clone` copies each field. -/
def OptionTimeStampCloneSpec : Prop := CloneIdAssumption (optionClone timeStampCloneInst)

/-! ## Calls that several statements name -/

/-- The vector `vec![sid]` that `get_auth_tokens` builds once and gives to both searches. -/
def sidVec (sid : utils.SecureUserId) : alloc.vec.Vec utils.SecureUserId :=
  sliceIntoVec (Std.Array.to_slice (Array.make 1#usize [sid]))

/-- The type of the set of unlocked users that `set_device_locked` changes. -/
abbrev UserSet : Type := HashSet utils.AndroidUserId RandomState alloc.alloc.Global

/-- The call `set.remove(&user)` of `set_device_locked`. The Lean function returns the new set, and
the generated code drops it. -/
noncomputable def userSetRemove (hs : UserSet) (user : utils.AndroidUserId) :
    Result (Bool × UserSet) :=
  HashSet.remove Insts.CoreCmpEq Insts.CoreHashHash buildHasher
    (borrowBlanket utils.AndroidUserId) Insts.CoreHashHash Insts.CoreCmpEq hs user

/-- The call `set.insert(user)` of `set_device_locked`. The Lean function returns the new set, and
the generated code drops it. -/
noncomputable def userSetInsert (hs : UserSet) (user : utils.AndroidUserId) :
    Result (Bool × UserSet) :=
  HashSet.insert Insts.CoreCmpEq Insts.CoreHashHash buildHasher hs user

/-! ## The choice of `super_encryption_required`

Each parameter gives a candidate: a priority and a type. `MaxBootLevel` has priority 3,
`UnlockedDeviceRequired` priority 2 and `UserSecureID` priority 1; the last two count only when
the domain is `APP` (`isApp`). Every other parameter has priority 0 and type `None`. The best
candidate so far is replaced only by a candidate of strictly greater priority, so the first of
the highest priority wins. -/

/-- The candidate of one parameter value: its priority and its type. -/
def superEncCandidate (isApp : Bool) : key_parameter.KeyParameterValue →
    Nat × super_key.SuperEncryptionType
  | .MaxBootLevel level => (3, .BootLevel (IScalar.hcast .Usize level))
  | .UnlockedDeviceRequired =>
    if isApp then (2, .UnlockedDeviceRequired) else (0, .None)
  | .UserSecureID _ =>
    if isApp then (1, .CredentialEncrypted) else (0, .None)
  | _ => (0, .None)

/-- The type chosen from the parameters, given the best candidate so far. -/
def superEncChoose (isApp : Bool) :
    List key_parameter.KeyParameter → Nat × super_key.SuperEncryptionType →
    super_key.SuperEncryptionType
  | [], (_, t) => t
  | kp :: rest, (p, t) =>
    if (superEncCandidate isApp kp.value).1 > p then
      superEncChoose isApp rest (superEncCandidate isApp kp.value)
    else superEncChoose isApp rest (p, t)

/-- The parameter value is one that depends on the domain. -/
def DomainDependent : key_parameter.KeyParameterValue → Prop
  | .UnlockedDeviceRequired => True
  | .UserSecureID _ => True
  | _ => False

end Keystore2Verify.Enforcements
