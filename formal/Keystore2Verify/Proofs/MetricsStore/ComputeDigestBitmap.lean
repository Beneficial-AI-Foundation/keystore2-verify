import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2

/-- exact: `compute_digest_bitmap` never fails. For the digest numbers 0 (NONE) to 6 (SHA_2_512),
which set the bit of the same number, the result has the bits of `bitmap` and the bit `k` set
(`digestBitPos` gives `k`). The argument `digest` is the `i32` newtype of the digest. -/
theorem compute_digest_bitmap_set (bitmap digest : Std.I32) (k : Nat)
    (hk : digestBitPos digest.val = some k) :
    ∃ r, metrics_store.compute_digest_bitmap bitmap digest = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k) := by
  sorry

/-- exact: `compute_digest_bitmap` never fails. For every other digest number, including every
number outside the AIDL enum, the bitmap is returned unchanged. -/
theorem compute_digest_bitmap_other (bitmap digest : Std.I32)
    (hk : digestBitPos digest.val = none) :
    metrics_store.compute_digest_bitmap bitmap digest = ok bitmap := by
  sorry

end Keystore2Verify.MetricsStore
