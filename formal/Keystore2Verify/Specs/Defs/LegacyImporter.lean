import Keystore2Verify.Specs.Defs.RemoteProvisioning

/-!
# Definitions for the statements about `legacy_importer.rs`

The list that `augment_legacy_characteristics_file_with_key_characteristics` computes, and the
description of the iterator over the legacy parameters that the statement takes as a hypothesis.
Nothing here is an axiom.
-/

namespace Keystore2Verify.LegacyImporter
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.RemoteProvisioning

/-- The vector after the loop: the parameters `xs` are taken in order, and a parameter is pushed
unless an element already in the vector (including one pushed earlier) has an equal value
(`eqv`). Only the value is compared, not the security level. -/
def augmentList
    (eqv : key_parameter.KeyParameterValue → key_parameter.KeyParameterValue → Bool) :
    List key_parameter.KeyParameter → List key_parameter.KeyParameter →
      List key_parameter.KeyParameter
  | acc, [] => acc
  | acc, x :: xs =>
    augmentList eqv (if acc.any (fun y => eqv y.value x.value) then acc else acc ++ [x]) xs

/-- The iterator type `It` of the instance `inst` behaves as an iterator over `items`: `view`
gives the elements that an iterator has left, `into_iter legacy` returns an iterator over
`items`, and `next` returns the first element left (or `None` when none is left) and an iterator
over the rest. This is a hypothesis about the type `T` that the function is called with. -/
def IteratesOver {T It : Type}
    (inst : core.iter.traits.collect.IntoIterator T key_parameter.KeyParameter It)
    (view : It → List key_parameter.KeyParameter) (legacy : T)
    (items : List key_parameter.KeyParameter) : Prop :=
  (∃ it, inst.into_iter legacy = ok it ∧ view it = items) ∧
  (∀ it, view it = [] →
    ∃ it', inst.iteratorInst.next it = ok (none, it') ∧ view it' = []) ∧
  (∀ it x xs, view it = x :: xs →
    ∃ it', inst.iteratorInst.next it = ok (some x, it') ∧ view it' = xs)

/-! ## Assumptions about the external functions on `String`

The derived methods of `RecentImport` and `SharedSecretParticipant` call these three. `String` is
the Lean string; the order is the order of Lean strings, which for valid UTF-8 text is the order of
the bytes that Rust compares. -/

/-- Assumption about an external function, over the function `clone`: it never panics and returns
a string equal to its argument. Idealisation: allocation never fails.
Record `ks2-ext-alloc-string-string-insts-corecloneclone-clone`. -/
def StringCloneAssumption (clone : String → Result String) : Prop :=
  ∀ s, clone s = ok s

/-- The closed instance of `StringCloneAssumption` for `String::clone` (record
`ks2-ext-alloc-string-string-insts-corecloneclone-clone`). -/
def StringCloneSpec : Prop :=
  StringCloneAssumption alloc.string.String.Insts.CoreCloneClone.clone

/-- Assumption about an external function, over the function `eq`: it never panics and returns
`true` exactly when the two strings are equal.
Record `ks2-ext-alloc-string-string-insts-corecmppartialeqstring-eq`. -/
def StringEqAssumption (eq : String → String → Result Bool) : Prop :=
  ∀ a b, eq a b = ok (decide (a = b))

/-- The closed instance of `StringEqAssumption` for `String::eq` (record
`ks2-ext-alloc-string-string-insts-corecmppartialeqstring-eq`). -/
def StringEqSpec : Prop :=
  StringEqAssumption alloc.string.String.Insts.CoreCmpPartialEqString.eq

/-- Assumption about an external function, over the function `cmp`: it never panics and returns
the order of the two strings.
Record `ks2-ext-alloc-string-string-insts-corecmpord-cmp`. -/
def StringCmpAssumption (cmp : String → String → Result Ordering) : Prop :=
  ∀ a b, cmp a b = ok (compare a b)

/-- The closed instance of `StringCmpAssumption` for `String::cmp` (record
`ks2-ext-alloc-string-string-insts-corecmpord-cmp`). -/
def StringCmpSpec : Prop :=
  StringCmpAssumption alloc.string.String.Insts.CoreCmpOrd.cmp

/-- The order of two imports: by `uid`, then by `alias`. -/
def recentImportOrd (x y : legacy_importer.RecentImport) : Ordering :=
  (compare x.uid.val y.uid.val).then (compare x.alias y.alias)

end Keystore2Verify.LegacyImporter
