import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open utils.Challenge.Insts
open CoreCmpPartialEqChallenge renaming eq → challengeEq
open CoreCloneClone renaming clone → challengeClone
open CoreCmpOrd renaming cmp → challengeCmp
open CoreCmpPartialOrdChallenge renaming partial_cmp → challengePartialCmp

/-- exact: `Challenge::eq` never fails and returns `true` exactly when the two numbers
are equal. -/
theorem challenge_eq (x y : utils.Challenge) :
    challengeEq x y = ok (decide (x = y)) := by
  sorry

/-- exact: `Challenge::clone` never fails and returns its argument. -/
theorem challenge_clone (x : utils.Challenge) : challengeClone x = ok x := by
  sorry

/-- exact: `Challenge::cmp` never fails. It compares the two numbers as signed integers. -/
theorem challenge_cmp (x y : utils.Challenge) :
    challengeCmp x y = ok (compare x.val y.val) := by
  sorry

/-- exact: `Challenge::partial_cmp` never fails and returns `Some` of the signed comparison of
the two numbers. -/
theorem challenge_partial_cmp (x y : utils.Challenge) :
    challengePartialCmp x y = ok (some (compare x.val y.val)) := by
  sorry

end Keystore2Verify.Utils
