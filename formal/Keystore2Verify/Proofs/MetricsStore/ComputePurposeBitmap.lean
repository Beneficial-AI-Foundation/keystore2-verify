import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2

/-- exact: `compute_purpose_bitmap` never fails. For the key purpose numbers 0 (ENCRYPT), 1
(DECRYPT), 2 (SIGN), 3 (VERIFY), 5 (WRAP_KEY), 6 (AGREE_KEY) and 7 (ATTEST_KEY), which set the
bits 1, 2, 3, 4, 5, 6 and 7, the result has the bits of `bitmap` and the bit `k` set
(`purposeBitPos` gives `k`). The argument `purpose` is the `i32` newtype of the key purpose. -/
theorem compute_purpose_bitmap_set (bitmap purpose : Std.I32) (k : Nat)
    (hk : purposeBitPos purpose.val = some k) :
    ∃ r, metrics_store.compute_purpose_bitmap bitmap purpose = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k) := by
  sorry

/-- exact: `compute_purpose_bitmap` never fails. For every other key purpose number, including every
number outside the AIDL enum, the bitmap is returned unchanged. -/
theorem compute_purpose_bitmap_other (bitmap purpose : Std.I32)
    (hk : purposeBitPos purpose.val = none) :
    metrics_store.compute_purpose_bitmap bitmap purpose = ok bitmap := by
  sorry

end Keystore2Verify.MetricsStore
