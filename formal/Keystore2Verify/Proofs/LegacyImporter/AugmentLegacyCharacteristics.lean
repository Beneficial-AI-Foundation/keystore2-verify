import Keystore2Verify.Specs.Defs.LegacyImporter

namespace Keystore2Verify.LegacyImporter
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.RemoteProvisioning
open legacy_importer renaming
  augment_legacy_characteristics_file_with_key_characteristics → augmentLegacy
open key_parameter.KeyParameterValue.Insts
  renaming CoreCmpPartialEqKeyParameterValue → valueEqInst
open legacy_importer.augment_legacy_characteristics_file_with_key_characteristics.closure.Insts
  renaming CoreOpsFunctionFnMutTupleShared0KeyParameterBool → augClosure

/-- conditional: the result is `from_km` followed by those parameters of `legacy`, in the order of
the iteration, whose value is not equal (`eqv`) to the value of any element already in the vector,
including a parameter pushed earlier in the same call (`augmentList`). Only the value is compared,
not the security level. A parameter that repeats a value is skipped, and for an empty `legacy` the
result is `from_km`. Hypotheses: the type `T` iterates over the list `items`
(`IteratesOver`); `eqv` is the result of the equality of two parameter values, which never fails;
the vector that the loop builds does not grow past the largest `usize` (`augmentList` is no longer
than `Usize.max`; a duplicate that is skipped does not count); the assumption about `Iter::any`
(`CoreSliceIterAnySpec`) for the closure of this function. -/
theorem augment_legacy_characteristics {T It : Type}
    (inst : core.iter.traits.collect.IntoIterator T key_parameter.KeyParameter It)
    (view : It → List key_parameter.KeyParameter)
    (eqv : key_parameter.KeyParameterValue → key_parameter.KeyParameterValue → Bool)
    (heq : ∀ a b, valueEqInst.eq a b = ok (eqv a b))
    (hany : CoreSliceIterAnySpec (augClosure inst))
    (from_km : alloc.vec.Vec key_parameter.KeyParameter) (legacy : T)
    (items : List key_parameter.KeyParameter) (hit : IteratesOver inst view legacy items)
    (hlen : (augmentList eqv from_km.val items).length ≤ Std.Usize.max) :
    ∃ v, augmentLegacy inst from_km legacy = ok v ∧
      v.val = augmentList eqv from_km.val items := by
  sorry

/-- conditional: if the vector that the loop builds would be longer than the largest `usize`
(`augmentList` has more than `Usize.max` elements), the first push past that length fails: the
function returns `fail maximumSizeExceeded`. Skipped duplicates do not count towards the length.
Hypotheses: as for `augment_legacy_characteristics` (the type `T` iterates over `items`; `eqv` is
the equality of parameter values, which never fails; the assumption about `Iter::any`). Not
stated: an iterator that never ends (the function then diverges, or fails at a push first); the
case is left open because the iterator is an arbitrary type `T`. -/
theorem augment_legacy_characteristics_overflow {T It : Type}
    (inst : core.iter.traits.collect.IntoIterator T key_parameter.KeyParameter It)
    (view : It → List key_parameter.KeyParameter)
    (eqv : key_parameter.KeyParameterValue → key_parameter.KeyParameterValue → Bool)
    (heq : ∀ a b, valueEqInst.eq a b = ok (eqv a b))
    (hany : CoreSliceIterAnySpec (augClosure inst))
    (from_km : alloc.vec.Vec key_parameter.KeyParameter) (legacy : T)
    (items : List key_parameter.KeyParameter) (hit : IteratesOver inst view legacy items)
    (hlen : Std.Usize.max < (augmentList eqv from_km.val items).length) :
    augmentLegacy inst from_km legacy = fail Error.maximumSizeExceeded := by
  sorry
