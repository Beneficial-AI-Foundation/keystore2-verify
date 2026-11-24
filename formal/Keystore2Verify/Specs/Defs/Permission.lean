import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `permission.rs`

The value tables of the two permission enums, bit sets, the key domains, and the context laws at
the `context` calls of the three `check_*` functions. Nothing here is an axiom.
-/

namespace Keystore2Verify.Permission
open Aeneas Aeneas.Std Result keystore2
open core.ffi.c_str
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay
open error.Error.Insts renaming CoreErrorError → KsErrorError
open keystore2_selinux.Error.Insts renaming CoreErrorError → SelinuxErrorError
open permission.KeyPerm.Insts
open anyhow.Error.Insts renaming AnyhowContextExtStdError → AnyhowExtStdError
open anyhow.context.ext.StdError renaming Blanket → StdBlanket
open permission.KeyPermSet.Insts.CoreConvertFromKeyPerm renaming «from» → setFromKeyPerm
open keystore2_selinux.Context.Insts.CoreOpsDerefDerefCStr renaming deref → contextDerefCStr
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode

/-- The view of a SELinux context as a `CStr`: the `deref` of `Context`. -/
noncomputable abbrev contextCStr : keystore2_selinux.Context → Result CStr :=
  contextDerefCStr

/-! ## Values of the permissions -/

/-- The number of a `KeyPerm`: the AIDL constant of the permission. `None` is 0. The value 1024
(`USE_NO_LSKF_BINDING`) has no variant. -/
def keyPermValue : permission.KeyPerm → Int
  | .None => 0
  | .Delete => 1
  | .GenUniqueId => 2
  | .GetInfo => 4
  | .Grant => 8
  | .ManageBlob => 16
  | .Rebind => 32
  | .ReqForcedOp => 64
  | .Update => 128
  | .Use => 256
  | .UseDevId => 512
  | .ConvertStorageKeyToEphemeral => 2048

/-- The numbers that `KeyPerm::from` maps to a variant other than `None`, and 0. -/
def keyPermNumbers : List Int := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 2048]

/-- The number of a `KeystorePerm`: 0 for `None`, then the bits 0 to 14 in declaration order. -/
def keystorePermValue : permission.KeystorePerm → Int
  | .None => 0
  | .AddAuth => 1
  | .ClearNs => 2
  | .List => 4
  | .Lock => 8
  | .Reset => 16
  | .Unlock => 32
  | .ChangeUser => 64
  | .ChangePassword => 128
  | .ClearUID => 256
  | .GetAuthToken => 512
  | .EarlyBootEnded => 1024
  | .PullMetrics => 2048
  | .DeleteAllKeys => 4096
  | .GetAttestationKey => 8192
  | .GetLastAuthTime => 16384

/-- The numbers that `KeystorePerm::from` maps to a variant other than `None`, and 0. -/
def keystorePermNumbers : List Int :=
  [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]

/-! ## Bit sets -/

/-- The bit set `a` contains every bit of `b`. -/
def Includes (a b : permission.KeyPermSet) : Prop := a &&& b = b

/-- Bit `i` of the set `s` is set. Bit 0 is the least significant bit, bit 31 the sign bit. -/
def HasBit (s : permission.KeyPermSet) (i : Nat) : Prop := s.bv.getLsbD i = true

/-- The `i32` with only bit `i` set: the value `1 << i`. -/
def bitVal (i : Nat) : Std.I32 := ⟨(1 : BitVec 32) <<< i⟩

/-- Bit `i` is the lowest set bit of `s` that is at position `pos` or above. -/
def NextBit (s : permission.KeyPermSet) (pos i : Nat) : Prop :=
  pos ≤ i ∧ i < 32 ∧ HasBit s i ∧ ∀ j, pos ≤ j → j < i → ¬ HasBit s j

/-! ## Key domains

The `Domain` of an AIDL key descriptor is an `i32`. The generated code compares it with these
numbers (`fvs-harness/aidl/android_system_keystore2/src/lib.rs`, lines 65 to 69). -/

/-- `Domain::APP` -/
def domainApp : Std.I32 := 0#i32
/-- `Domain::GRANT` -/
def domainGrant : Std.I32 := 1#i32
/-- `Domain::SELINUX` -/
def domainSelinux : Std.I32 := 2#i32
/-- `Domain::BLOB` -/
def domainBlob : Std.I32 := 3#i32
/-- `Domain::KEY_ID` -/
def domainKeyId : Std.I32 := 4#i32

open android_system_keystore2.aidl.android.system.keystore2 in
/-- The key descriptor of the AIDL interface. -/
abbrev KeyDesc := KeyDescriptor.KeyDescriptor

/-! ## Errors that the functions build -/

/-- `keystore2::error::Error::sys()`: the keystore2 error with the response code `SYSTEM_ERROR`. -/
def sysError : error.Error :=
  .Rc SYSTEM_ERROR

/-- The keystore2 error with the response code `INVALID_ARGUMENT`. -/
def invalidArgumentError : error.Error :=
  .Rc INVALID_ARGUMENT

/-- The root cause `selinux::Error::perm()`. -/
def deniedRoot : ErrRoot := .selinux .PermissionDenied

/-! ## The `context` calls

One abbreviation for each kind of `.context(..)` call in `permission.rs`. They all instantiate
`ResultContextLaw`. The first word says what the error is before the call: `anyhow` for an
`anyhow::Error`, `selinux` or `ks` for a wrapped error. The second says whether the message is a
`&str` constant or a `String` made by `format!` or `ks_err!`. -/

open core.result.Result.Insts.AnyhowContext in
/-- A call `r.context("..")` on a result that holds an `anyhow::Error` and a `T`. The new error
has the root cause of the old one. -/
abbrev AnyhowStrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw root root
    (context (T := T) AnyhowExtStdError
      (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay))

open core.result.Result.Insts.AnyhowContext in
/-- A call `r.context(s)` with a `String` message on a result that holds an `anyhow::Error` and
a `T`. The new error has the root cause of the old one. -/
abbrev AnyhowStringCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw root root
    (context (T := T) AnyhowExtStdError
      StringDisplay)

open core.result.Result.Insts.AnyhowContext in
/-- A call `Err(selinux_error).context("..")`. The root cause of the new error is the SELinux
error. -/
abbrev SelinuxStrCtxLaw (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw (fun x => ErrRoot.selinux x) root
    (context (T := Unit)
      (StdBlanket SelinuxErrorError)
      (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay))

open core.result.Result.Insts.AnyhowContext in
/-- A call `Err(selinux_error).context(format!(..))`. The root cause of the new error is the
SELinux error. -/
abbrev SelinuxStringCtxLaw (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw (fun x => ErrRoot.selinux x) root
    (context (T := Unit)
      (StdBlanket SelinuxErrorError)
      StringDisplay)

open core.result.Result.Insts.AnyhowContext in
/-- A call `Err(keystore2_error).context(..)` with a `String` message. The root cause of the new
error is the keystore2 error. -/
abbrev KsStringCtxLaw (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw (fun x => ErrRoot.ks x) root
    (context (T := Unit)
      (StdBlanket KsErrorError)
      StringDisplay)

/-! ## Coverage by an access vector -/

/-- Bit `i` is a bit that is no `KeyPerm`: bit 10 (`USE_NO_LSKF_BINDING`) and bits 12 to 31.
`KeyPerm::from(1 << i)` is `KeyPerm::None` for exactly these bits (and for no other bit). -/
def UnknownBit (i : Nat) : Prop := i = 10 ∨ (12 ≤ i ∧ i < 32)

/-- The access vector covers `perm`: it is `some s`, and `s` includes the bit set of `perm`. -/
def Covers (perm : permission.KeyPerm) (access_vector : Option permission.KeyPermSet) : Prop :=
  ∃ s o, access_vector = some s ∧
    setFromKeyPerm perm = ok o ∧ Includes s o

end Keystore2Verify.Permission
