import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.LegacyKeyCharacteristics.Insts
open alloc.vec.CloneVec renaming clone → vecClone
open alloc.vec.partial_eq.PartialEqVec renaming eq → vecEq
open alloc.vec.Vec.Insts.CoreCmpOrd renaming cmp → vecCmp
open CoreCloneClone renaming clone → lkcClone
open CoreCmpPartialEqLegacyKeyCharacteristics renaming eq → lkcEq
open CoreCmpOrd renaming cmp → lkcCmp
open CoreCmpPartialOrdLegacyKeyCharacteristics renaming partial_cmp → lkcPartialCmp
open key_parameter.KeyParameter.Insts renaming CoreCloneClone.clone → kpClone
open key_parameter.KeyParameter.Insts renaming CoreCloneClone → kpCloneInst
open key_parameter.KeyParameter.Insts renaming CoreCmpOrd → kpOrdInst
open key_parameter.KeyParameter.Insts renaming CoreCmpPartialEqKeyParameter → kpEqInst

/-- exact: the clone of `Cache v` is a `Cache` of the element-wise clone of `v`, and it returns
exactly when that clone does. -/
theorem lkc_clone_cache (v : alloc.vec.Vec key_parameter.KeyParameter)
    (r : legacy_blob.LegacyKeyCharacteristics) :
    lkcClone (.Cache v) = ok r ↔ ∃ v', vecClone kpCloneInst v = ok v' ∧
      r = .Cache v' := by
  sorry

/-- exact: the clone of `File v` is a `File` of the element-wise clone of `v`, and it returns
exactly when that clone does. -/
theorem lkc_clone_file (v : alloc.vec.Vec key_parameter.KeyParameter)
    (r : legacy_blob.LegacyKeyCharacteristics) :
    lkcClone (.File v) = ok r ↔ ∃ v', vecClone kpCloneInst v = ok v' ∧
      r = .File v' := by
  sorry

/-- conditional: if cloning a `KeyParameter` always returns an equal value, the clone of a
`LegacyKeyCharacteristics` returns an equal value. Hypothesis: the clone of `KeyParameter`
(keystore2's own translated function) returns its argument for every `KeyParameter`. -/
theorem lkc_clone_eq (hkp : ∀ x, kpClone x = ok x) (x : legacy_blob.LegacyKeyCharacteristics) :
    lkcClone x = ok x := by
  sorry

/-- exact: a `Cache` and a `File` are never equal. -/
theorem lkc_eq_variant_ne (a b : legacy_blob.LegacyKeyCharacteristics)
    (h : characteristicsIndex a ≠ characteristicsIndex b) : lkcEq a b = ok false := by
  sorry

/-- exact: two `Cache` values are equal when the two vectors are: the vectors have the same
length and the elements are equal pairwise, as the generated comparison of `KeyParameter` says. -/
theorem lkc_eq_cache (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcEq (.Cache a) (.Cache b) =
      vecEq kpEqInst a b := by
  sorry

/-- exact: two `File` values are equal when the two vectors are, as for `Cache`. -/
theorem lkc_eq_file (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcEq (.File a) (.File b) =
      vecEq kpEqInst a b := by
  sorry

/-- exact: a `Cache` is smaller than a `File`. The comparison looks at no element. -/
theorem lkc_cmp_cache_file (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.Cache a) (.File b) = ok Ordering.lt := by
  sorry

/-- exact: a `File` is greater than a `Cache`. The comparison looks at no element. -/
theorem lkc_cmp_file_cache (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.File a) (.Cache b) = ok Ordering.gt := by
  sorry

/-- exact: two `Cache` values are compared as their vectors: element by element, a shorter
prefix being smaller. The comparison of vectors is an external function, so this statement says
nothing about its result. -/
theorem lkc_cmp_cache (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.Cache a) (.Cache b) =
      vecCmp alloc.alloc.Global kpOrdInst a b := by
  sorry

/-- exact: two `File` values are compared as their vectors, as for `Cache`. -/
theorem lkc_cmp_file (a b : alloc.vec.Vec key_parameter.KeyParameter) :
    lkcCmp (.File a) (.File b) =
      vecCmp alloc.alloc.Global kpOrdInst a b := by
  sorry

/-- exact: `partial_cmp` never returns `None`. It returns `Some o` exactly when `cmp` returns
`o`, and it fails exactly when `cmp` fails. -/
theorem lkc_partial_cmp (a b : legacy_blob.LegacyKeyCharacteristics)
    (r : Option Ordering) :
    lkcPartialCmp a b = ok r ↔ ∃ o, lkcCmp a b = ok o ∧ r = some o := by
  sorry

/-- conditional: two values of the same variant are equal exactly when their vectors are equal.
Hypothesis: comparing two key parameters returns `true` exactly when they are equal (a statement
about the translated comparison of `KeyParameter`, which rests on external comparisons of
the AIDL enums). -/
theorem lkc_eq_content
    (hkp : ∀ x y, ∃ r, kpEqInst.eq x y = ok r ∧ (r = true ↔ x = y))
    (a b : legacy_blob.LegacyKeyCharacteristics)
    (h : characteristicsIndex a = characteristicsIndex b) :
    ∃ r, lkcEq a b = ok r ∧ (r = true ↔ lkcList a = lkcList b) := by
  sorry

/-- conditional: the comparison of two values is `lkcOrder c`: `Cache` before `File`, and two
values of one variant ordered as their vectors, element by element, a proper prefix being
smaller (so two empty vectors are equal). Hypotheses: comparing two key parameters returns
`c x y`, and the assumption about the comparison of vectors, an external function
(`VecCmpSpec`). -/
theorem lkc_cmp_order
    (c : key_parameter.KeyParameter → key_parameter.KeyParameter → Ordering)
    (hc : ∀ x y, kpOrdInst.cmp x y = ok (c x y)) (hv : VecCmpSpec c)
    (a b : legacy_blob.LegacyKeyCharacteristics) :
    lkcCmp a b = ok (lkcOrder c a b) := by
  sorry

/-- conditional: `partial_cmp` returns `Some` of `lkcOrder c`. Hypotheses: those of
`lkc_cmp_order`. -/
theorem lkc_partial_cmp_order
    (c : key_parameter.KeyParameter → key_parameter.KeyParameter → Ordering)
    (hc : ∀ x y, kpOrdInst.cmp x y = ok (c x y)) (hv : VecCmpSpec c)
    (a b : legacy_blob.LegacyKeyCharacteristics) :
    lkcPartialCmp a b = ok (some (lkcOrder c a b)) := by
  sorry

end Keystore2Verify.LegacyBlob
