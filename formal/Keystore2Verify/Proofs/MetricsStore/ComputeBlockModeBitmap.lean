import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2

/-- exact: `compute_block_mode_bitmap` never fails. For the block mode numbers 1 (ECB), 2 (CBC), 3
(CTR) and 32 (GCM), which set the bits 1, 2, 3 and 4, the result has the bits of `bitmap` and the
bit `k` set (`blockModeBitPos` gives `k`). The argument `block_mode` is the `i32` newtype of the
block mode. -/
theorem compute_block_mode_bitmap_set (bitmap block_mode : Std.I32) (k : Nat)
    (hk : blockModeBitPos block_mode.val = some k) :
    ∃ r, metrics_store.compute_block_mode_bitmap bitmap block_mode = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k) := by
  sorry

/-- exact: `compute_block_mode_bitmap` never fails. For every other block mode number, including
every number outside the AIDL enum, the bitmap is returned unchanged. -/
theorem compute_block_mode_bitmap_other (bitmap block_mode : Std.I32)
    (hk : blockModeBitPos block_mode.val = none) :
    metrics_store.compute_block_mode_bitmap bitmap block_mode = ok bitmap := by
  sorry

end Keystore2Verify.MetricsStore
