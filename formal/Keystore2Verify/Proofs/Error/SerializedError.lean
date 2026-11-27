import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open error.SerializedError.Insts
open CoreCloneClone renaming clone → serializedClone
open CoreCmpPartialEqSerializedError renaming eq → serializedEq
open CoreCmpOrd renaming cmp → serializedCmp
open CoreCmpPartialOrdSerializedError renaming partial_cmp → serializedPartialCmp

/-- exact: `SerializedError::clone` returns a copy of the code. -/
theorem SerializedError_clone (x : error.SerializedError) : serializedClone x = ok x := by
  sorry

/-- exact: `SerializedError::eq` returns `true` exactly when the two codes are equal. -/
theorem SerializedError_eq (x y : error.SerializedError) :
    serializedEq x y = ok (decide (x = y)) := by
  sorry

/-- exact: `SerializedError::cmp` compares the codes as signed 32-bit numbers. -/
theorem SerializedError_cmp (x y : error.SerializedError) :
    serializedCmp x y = ok (compare x.val y.val) := by
  sorry

/-- exact: `SerializedError::partial_cmp` always returns `Some` of the comparison of the codes as
signed 32-bit numbers. -/
theorem SerializedError_partial_cmp (x y : error.SerializedError) :
    serializedPartialCmp x y = ok (some (compare x.val y.val)) := by
  sorry

end Keystore2Verify.Error
