import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open legacy_blob.Error.Insts renaming CoreCmpPartialEqError.eq → errorEq

/-- exact: `eq` never fails. It returns `true` exactly when the two errors are the same variant
(the derived comparison of the discriminants). -/
theorem legacy_blob_error_eq (a b : legacy_blob.Error) :
    errorEq a b = ok (decide (errorIndex a = errorIndex b)) := by
  sorry

end Keystore2Verify.LegacyBlob
