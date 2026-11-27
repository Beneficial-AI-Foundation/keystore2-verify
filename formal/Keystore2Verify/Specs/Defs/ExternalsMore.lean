import Keystore2Verify.Specs.Defs.Externals

/-!
# Assumptions about external functions that several spec files share

An assumption here is used by the statements of more than one Rust file. Each closed assumption
cites one externals record, and is the only closed proposition that cites it. The spec files use it
through an abbreviation of their own. Nothing here is an axiom and nothing is proved.
-/

namespace Keystore2Verify.ExternalsMore
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- Assumption about an external function, over the function `clone`: `clone t` never panics and
returns a value equal to `t`. -/
def HardwareAuthTokenCloneAssumption
    (clone : HardwareAuthToken.HardwareAuthToken →
      Result HardwareAuthToken.HardwareAuthToken) : Prop :=
  ∀ t, clone t = ok t

/-- Assumption about an external function: the clone of a `HardwareAuthToken` (record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-hardwareauthtoken-hardwareauthtoken-insts-corecloneclone-clone`).
It is `HardwareAuthTokenCloneAssumption` at the extracted symbol. Idealisation: allocation never
fails (the clone copies the `mac` vector). Source: the AIDL stand-in derives `Clone` for
`HardwareAuthToken`, and a derived clone copies each field. -/
def HardwareAuthTokenCloneSpec : Prop :=
  HardwareAuthTokenCloneAssumption HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone.clone

/-- Assumption about an external function, over the function `must_use`: the call never panics and
returns its argument. -/
def AnyhowMustUseAssumption (must_use : anyhow.Error → Result anyhow.Error) : Prop :=
  ∀ e : anyhow.Error, must_use e = ok e

/-- Assumption about an external function: `anyhow::__private::must_use` (record
`ks2-ext-anyhow-private-must-use`) never panics and returns its argument. It is
`AnyhowMustUseAssumption` at the extracted symbol. Source: anyhow's `must_use` returns the error it
is given. -/
def AnyhowMustUseSpec : Prop := AnyhowMustUseAssumption anyhow.__private.must_use

end Keystore2Verify.ExternalsMore
