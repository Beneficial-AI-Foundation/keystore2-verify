import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `remote_provisioning.rs`

The meaning of a result of a system property read, the key parameters that make a key
asymmetric, and the assumption about the external function `Iterator::any` that
`is_asymmetric_key` calls on a slice iterator. Nothing here is an axiom.
-/

namespace Keystore2Verify.RemoteProvisioning
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- A boolean property read: the value if the read succeeded, and `false` if it failed. -/
def propBool {E : Type} : core.result.Result Bool E → Bool
  | .Ok b => b
  | .Err _ => false

/-- The key parameter is `Tag::ALGORITHM` (268435458) with the value `Algorithm(a)`, and `a` is
RSA (1), EC (3) or ML_DSA (4). These are the numbers that the generated code uses. -/
def IsAsymParam (p : KeyParameter.KeyParameter) : Prop :=
  p.tag = 268435458#i32 ∧
  ∃ a, p.value = KeyParameterValue.KeyParameterValue.Algorithm a ∧
    (a = 1#i32 ∨ a = 3#i32 ∨ a = 4#i32)

/-- The elements that a slice iterator has left: those of its slice from its position on. -/
def remaining {T : Type} (it : core.slice.iter.Iter T) : List T := List.drop it.i it.slice.val

/-- Assumption about an external function, over the function `any` and the closure instance
`inst`: if the closure with the state `c` returns `(p x, c)` for each remaining element `x` (a
predicate `p` that leaves the state unchanged and never fails), then `any it c` never panics, and
it returns `true` exactly when some remaining element satisfies `p`. The returned iterator is
not constrained.
Record `ks2-ext-core-slice-iter-iter-insts-coreitertraitsiteratoriteratorsharedat-any`. -/
def IterAnyAssumption {T F : Type} (inst : core.ops.function.FnMut F T Bool)
    (any : core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)) : Prop :=
  ∀ (it : core.slice.iter.Iter T) (c : F) (p : T → Bool),
    (∀ x ∈ remaining it, inst.call_mut c x = ok (p x, c)) →
    ∃ b it', any it c = ok (b, it') ∧ (b = true ↔ ∃ x ∈ remaining it, p x = true)

/-- The closed instance of `IterAnyAssumption` for `Iter::any` of a slice iterator (record
`ks2-ext-core-slice-iter-iter-insts-coreitertraitsiteratoriteratorsharedat-any`). -/
def CoreSliceIterAnySpec {T F : Type} (inst : core.ops.function.FnMut F T Bool) : Prop :=
  IterAnyAssumption inst
    (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any inst)

end Keystore2Verify.RemoteProvisioning
