import Keystore2Verify.Specs.Defs.LegacyImporter

/-!
# Definitions for the statements about `shared_secret_negotiation.rs`

The order of two participants, and the assumptions about the external functions on `bool` and on
pairs of `usize` that the derived methods call. The assumptions about `String` are in the file for
`legacy_importer.rs`. Nothing here is an axiom.
-/

namespace Keystore2Verify.SharedSecretNegotiation
open Aeneas Aeneas.Std Result keystore2
open shared_secret_negotiation

/-- Assumption about an external function, over the function `cmp`: it never panics and returns
the order of the two booleans, with `false` before `true`.
Record `ks2-ext-bool-insts-corecmpord-cmp`. -/
def BoolCmpAssumption (cmp : Bool → Bool → Result Ordering) : Prop :=
  ∀ a b, cmp a b = ok (compare a b)

/-- The closed instance of `BoolCmpAssumption` for `bool::cmp` (record
`ks2-ext-bool-insts-corecmpord-cmp`). -/
def BoolCmpSpec : Prop := BoolCmpAssumption Bool.Insts.CoreCmpOrd.cmp

/-- A pair of `usize` numbers, here the pair `(major, minor)` of a version. -/
abbrev UsizePair : Type := Std.Usize × Std.Usize

/-- Assumption about an external function, over the function `eq`: on pairs of `usize` it never
panics and returns `true` exactly when the two pairs are equal.
Record `ks2-ext-pair-insts-corecmppartialeqpair-eq`. -/
def PairEqAssumption (eq : UsizePair → UsizePair → Result Bool) : Prop :=
  ∀ p q, eq p q = ok (decide (p = q))

/-- The closed instance of `PairEqAssumption` for the equality of pairs at the instances
`PartialEq<usize>` (record `ks2-ext-pair-insts-corecmppartialeqpair-eq`). -/
def PairEqSpec : Prop :=
  PairEqAssumption
    (Pair.Insts.CoreCmpPartialEqPair.eq core.cmp.PartialEqUsize core.cmp.PartialEqUsize)

/-- The lexicographic order of two pairs of `usize`: the first components, then the second. -/
def pairOrd (p q : UsizePair) : Ordering :=
  (compare p.1.val q.1.val).then (compare p.2.val q.2.val)

/-- Assumption about an external function, over the function `cmp`: on pairs of `usize` it never
panics and returns the lexicographic order of the two pairs.
Record `ks2-ext-pair-insts-corecmpord-cmp`. -/
def PairCmpAssumption (cmp : UsizePair → UsizePair → Result Ordering) : Prop :=
  ∀ p q, cmp p q = ok (pairOrd p q)

/-- The closed instance of `PairCmpAssumption` for the order of pairs at the instances `Ord<usize>`
(record `ks2-ext-pair-insts-corecmpord-cmp`). -/
def PairCmpSpec : Prop :=
  PairCmpAssumption (Pair.Insts.CoreCmpOrd.cmp core.cmp.OrdUsize core.cmp.OrdUsize)

/-- The order of two participants: `Aidl` before `Hidl` (the declaration order), then by the
fields in order: the name for `Aidl`; the flag (`false` before `true`) and then the pair for
`Hidl`. -/
def participantOrd : SharedSecretParticipant → SharedSecretParticipant → Ordering
  | .Aidl s, .Aidl t => compare s t
  | .Aidl _, .Hidl _ _ => .lt
  | .Hidl _ _, .Aidl _ => .gt
  | .Hidl b p, .Hidl c q => (compare b c).then (pairOrd p q)

end Keystore2Verify.SharedSecretNegotiation
