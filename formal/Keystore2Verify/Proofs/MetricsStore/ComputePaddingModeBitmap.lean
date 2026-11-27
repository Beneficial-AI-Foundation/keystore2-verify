import Keystore2Verify.Specs.Defs.MetricsStore

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2

/-- exact: `compute_padding_mode_bitmap` never fails. For the padding mode numbers 1 (NONE), 2
(RSA_OAEP), 3 (RSA_PSS), 4 (RSA_PKCS1_1_5_ENCRYPT), 5 (RSA_PKCS1_1_5_SIGN) and 64 (PKCS7), which
set the bits 0 to 5 in this order, the result has the bits of `bitmap` and the bit `k` set
(`paddingBitPos` gives `k`). The argument `padding_mode` is the `i32` newtype of the padding
mode. -/
theorem compute_padding_mode_bitmap_set (bitmap padding_mode : Std.I32) (k : Nat)
    (hk : paddingBitPos padding_mode.val = some k) :
    ∃ r, metrics_store.compute_padding_mode_bitmap bitmap padding_mode = ok r ∧
      r.bv = bitmap.bv ||| (1#32 <<< k) := by
  sorry

/-- exact: `compute_padding_mode_bitmap` never fails. For every other padding mode number, including
every number outside the AIDL enum, the bitmap is returned unchanged. -/
theorem compute_padding_mode_bitmap_other (bitmap padding_mode : Std.I32)
    (hk : paddingBitPos padding_mode.val = none) :
    metrics_store.compute_padding_mode_bitmap bitmap padding_mode = ok bitmap := by
  sorry

end Keystore2Verify.MetricsStore
