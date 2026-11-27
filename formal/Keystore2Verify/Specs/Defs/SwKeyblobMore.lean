import Keystore2Verify.Specs.Defs.SwKeyblob

/-!
# Definitions for the statements about the equality of `sw_keyblob::KeyBlob`

The equality of two key blobs compares the key material and the two lists of key parameters.
The file adds one assumption about an external function (the equality of two `KeyParameter`
values). Nothing here is an axiom.
-/

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open KeyParameter.KeyParameter.Insts.CoreCmpPartialEqKeyParameter renaming eq → keyParamEq

/-- Assumption about an external function, over the function `eq`: `eq x y` never panics, and it
returns `true` exactly when `x = y`. -/
def KeyParameterEqAssumption (eq : KeyParam → KeyParam → Result Bool) : Prop :=
  ∀ x y, ∃ r, eq x y = ok r ∧ (r = true ↔ x = y)

/-- Assumption about an external function: the equality of two `KeyParameter` values (register
record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-keyparameter-keyparameter-insts-corecmppartialeqkeyparameter-eq`).
It is `KeyParameterEqAssumption` at the extracted symbol. Source: the AIDL stand-in derives
`PartialEq` for `KeyParameter`, and a derived equality compares each field. -/
def KeyParameterEqSpec : Prop :=
  KeyParameterEqAssumption keyParamEq

end Keystore2Verify.SwKeyblob
