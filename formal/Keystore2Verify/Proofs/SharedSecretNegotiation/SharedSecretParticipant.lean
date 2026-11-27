import Keystore2Verify.Specs.Defs.SharedSecretNegotiation

namespace Keystore2Verify.SharedSecretNegotiation
open Aeneas Aeneas.Std Result keystore2
open shared_secret_negotiation
open Keystore2Verify.LegacyImporter
open SharedSecretParticipant.Insts

/-- conditional: if cloning the name `s` of an `Aidl` participant returns `s'`, `clone` returns
`Aidl s'`. Hypothesis: the outcome of `String::clone`; for a faithful clone `s'` equals `s`. -/
theorem participant_clone_aidl (s s' : String)
    (h : alloc.string.String.Insts.CoreCloneClone.clone s = ok s') :
    CoreCloneClone.clone (SharedSecretParticipant.Aidl s) =
      ok (SharedSecretParticipant.Aidl s') := by
  sorry

/-- exact: `clone` of a `Hidl` participant returns an equal participant (the flag and the pair of
numbers are copied). -/
theorem participant_clone_hidl (b : Bool) (p : Std.Usize × Std.Usize) :
    CoreCloneClone.clone (SharedSecretParticipant.Hidl b p) =
      ok (SharedSecretParticipant.Hidl b p) := by
  sorry

/-- exact: participants of different variants are not equal: `eq` returns `false`. -/
theorem participant_eq_variants_differ (s : String) (b : Bool) (p : Std.Usize × Std.Usize) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Aidl s) (.Hidl b p) = ok false ∧
    CoreCmpPartialEqSharedSecretParticipant.eq (.Hidl b p) (.Aidl s) = ok false := by
  sorry

/-- exact: for two `Aidl` participants, `eq` returns what `String::eq` returns for the names. -/
theorem participant_eq_aidl (s t : String) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Aidl s) (.Aidl t) =
      alloc.string.String.Insts.CoreCmpPartialEqString.eq s t := by
  sorry

/-- exact: for two `Hidl` participants whose flags differ, `eq` returns `false`. -/
theorem participant_eq_hidl_flag (b c : Bool) (p q : Std.Usize × Std.Usize) (h : b ≠ c) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Hidl b p) (.Hidl c q) = ok false := by
  sorry

/-- exact: for two `Hidl` participants with the same flag, `eq` returns what the equality of the
pairs `(major, minor)` returns. -/
theorem participant_eq_hidl_pair (b : Bool) (p q : Std.Usize × Std.Usize) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Hidl b p) (.Hidl b q) =
      Pair.Insts.CoreCmpPartialEqPair.eq core.cmp.PartialEqUsize core.cmp.PartialEqUsize p q := by
  sorry

/-- exact: an `Aidl` participant is less than a `Hidl` participant (the variants are ordered by
declaration), and the other way round is greater. -/
theorem participant_cmp_variants_differ (s : String) (b : Bool) (p : Std.Usize × Std.Usize) :
    CoreCmpOrd.cmp (.Aidl s) (.Hidl b p) = ok Ordering.lt ∧
    CoreCmpOrd.cmp (.Hidl b p) (.Aidl s) = ok Ordering.gt := by
  sorry

/-- exact: for two `Aidl` participants, `cmp` returns what `String::cmp` returns for the names. -/
theorem participant_cmp_aidl (s t : String) :
    CoreCmpOrd.cmp (.Aidl s) (.Aidl t) = alloc.string.String.Insts.CoreCmpOrd.cmp s t := by
  sorry

/-- conditional: for two `Hidl` participants, if the comparison of the flags (`false` is less than
`true`) returns `Less` or `Greater`, `cmp` returns it. Hypothesis: the outcome of `bool::cmp`. -/
theorem participant_cmp_hidl_flag (b c : Bool) (p q : Std.Usize × Std.Usize) (o : Ordering)
    (h : Bool.Insts.CoreCmpOrd.cmp b c = ok o) (ho : o ≠ Ordering.eq) :
    CoreCmpOrd.cmp (.Hidl b p) (.Hidl c q) = ok o := by
  sorry

/-- conditional: for two `Hidl` participants, if the flags compare equal, `cmp` returns what the
lexicographic comparison of the pairs `(major, minor)` returns. Hypothesis: the outcome of
`bool::cmp` on the flags. -/
theorem participant_cmp_hidl_pair (b c : Bool) (p q : Std.Usize × Std.Usize)
    (h : Bool.Insts.CoreCmpOrd.cmp b c = ok Ordering.eq) :
    CoreCmpOrd.cmp (.Hidl b p) (.Hidl c q) =
      Pair.Insts.CoreCmpOrd.cmp core.cmp.OrdUsize core.cmp.OrdUsize p q := by
  sorry

/-- conditional: if `cmp x y` returns `o`, `partial_cmp x y` returns `Some o`. Hypothesis: the
outcome of `cmp`. If `cmp` fails, so does `partial_cmp`. -/
theorem participant_partial_cmp (x y : SharedSecretParticipant) (o : Ordering)
    (h : CoreCmpOrd.cmp x y = ok o) :
    CoreCmpPartialOrdSharedSecretParticipant.partial_cmp x y = ok (some o) := by
  sorry

/-- conditional: `clone x` returns a copy of `x`: the same variant with the same fields.
Hypothesis: the assumption about `String::clone` (`StringCloneSpec`). -/
theorem participant_clone_eq (hs : StringCloneSpec) (x : SharedSecretParticipant) :
    CoreCloneClone.clone x = ok x := by
  sorry

/-- conditional: `eq x y` returns `true` exactly when `x` and `y` are the same variant with equal
fields. It never fails. Hypotheses: the assumptions about `String::eq` (`StringEqSpec`) and about
the equality of pairs of `usize` (`PairEqSpec`). -/
theorem participant_eq_iff (hs : StringEqSpec) (hp : PairEqSpec) (x y : SharedSecretParticipant) :
    ∃ b, CoreCmpPartialEqSharedSecretParticipant.eq x y = ok b ∧ (b = true ↔ x = y) := by
  sorry

/-- conditional: `cmp x y` is the lexicographic order: `Aidl` before `Hidl`, and then the fields in
order (`participantOrd`). It never fails. Hypotheses: the assumptions about `String::cmp`
(`StringCmpSpec`), `bool::cmp` (`BoolCmpSpec`) and the order of pairs of `usize`
(`PairCmpSpec`). -/
theorem participant_cmp_lex (hs : StringCmpSpec) (hb : BoolCmpSpec) (hp : PairCmpSpec)
    (x y : SharedSecretParticipant) :
    CoreCmpOrd.cmp x y = ok (participantOrd x y) := by
  sorry

/-- conditional: `partial_cmp x y` returns `Some` of the lexicographic order (`participantOrd`).
It never fails. Hypotheses: the assumptions about `String::cmp` (`StringCmpSpec`), `bool::cmp`
(`BoolCmpSpec`) and the order of pairs of `usize` (`PairCmpSpec`). -/
theorem participant_partial_cmp_lex (hs : StringCmpSpec) (hb : BoolCmpSpec) (hp : PairCmpSpec)
    (x y : SharedSecretParticipant) :
    CoreCmpPartialOrdSharedSecretParticipant.partial_cmp x y = ok (some (participantOrd x y)) := by
  sorry
