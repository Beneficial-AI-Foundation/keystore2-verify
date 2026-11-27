import Keystore2Verify.Specs.Defs.KmCompat

namespace Keystore2Verify.KmCompat
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2.core.slice.Slice renaming starts_with → sliceStartsWith
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming eq → sliceVecEq
open km_compat renaming wrap_keyblob → wrapKeyblob, unwrap_keyblob → unwrapKeyblob

/-- conditional: if `hmac_sha256` of the wrapper key and `keyblob` returns the tag `tag`, then
`wrap_keyblob` returns the prefix `SoftKeyMintForV1Blob`, then `keyblob`, then `tag`.
Hypotheses: the assumptions `AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (in
the Rust source the error message is built before the result of `hmac_sha256` is examined) and
the assumption `CryptoCtxLaw` about `context`; the value `n` of `HMAC_SHA256_LEN`, which sizes
the buffer, and that the buffer size and the result fit in `usize`; and the outcome of
`hmac_sha256`. -/
theorem wrap_keyblob_ok (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (root : anyhow.Error → ErrRoot) (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (keyblob : Slice Std.U8) (n : Std.Usize)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (tag : alloc.vec.Vec Std.U8)
    (hfit : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + tag.val.length
      ≤ Std.Usize.max)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = ok (.Ok tag)) :
    ∃ v, wrapKeyblob keyblob = ok (.Ok v) ∧
      v.val = km_compat.KEYBLOB_PREFIX.val ++ keyblob.val ++ tag.val := by
  sorry

/-- conditional: if `hmac_sha256` returns the crypto error `x`, then `wrap_keyblob` returns an error
whose root cause is `x`. Hypotheses: those of `wrap_keyblob_ok`, except that `hmac_sha256`
returns `Err x`. The message of the error is not stated. -/
theorem wrap_keyblob_err (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (root : anyhow.Error → ErrRoot) (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (keyblob : Slice Std.U8) (n : Std.Usize)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (x : keystore2_crypto.error.Error)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = ok (.Err x)) :
    ∃ e, wrapKeyblob keyblob = ok (.Err e) ∧ root e = ErrRoot.crypto x := by
  sorry

/-- conditional: if `hmac_sha256` fails with `x`, then `wrap_keyblob` fails with `x`. Hypotheses:
the value `n` of `HMAC_SHA256_LEN`, that the buffer size fits in `usize`, and the outcome of
`hmac_sha256`. -/
theorem wrap_keyblob_fail_hmac (keyblob : Slice Std.U8) (n : Std.Usize) (x : Error)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = fail x) :
    wrapKeyblob keyblob = fail x := by
  sorry

/-- conditional: if the prefix and `keyblob` together are longer than `usize` can hold, then
`wrap_keyblob` fails with an integer overflow. Hypothesis: the first length sum is too large. -/
theorem wrap_keyblob_fail_len_add (keyblob : Slice Std.U8)
    (hover : Std.Usize.max < km_compat.KEYBLOB_PREFIX.length + keyblob.val.length) :
    wrapKeyblob keyblob = fail .integerOverflow := by
  sorry

/-- conditional: if the prefix and `keyblob` fit, and adding the value `n` of `HMAC_SHA256_LEN`
overflows `usize`, then `wrap_keyblob` fails with an integer overflow.
Hypotheses: the first sum fits, the outcome `n` of `HMAC_SHA256_LEN`, and that the second sum is
too large. -/
theorem wrap_keyblob_fail_cap_add (keyblob : Slice Std.U8) (n : Std.Usize)
    (hfit : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length ≤ Std.Usize.max)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hover : Std.Usize.max < km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val) :
    wrapKeyblob keyblob = fail .integerOverflow := by
  sorry

/-- conditional: if `HMAC_SHA256_LEN` fails with `x`, then `wrap_keyblob` fails with `x`.
Hypotheses: the prefix and `keyblob` fit in `usize`, and the outcome of `HMAC_SHA256_LEN`. -/
theorem wrap_keyblob_fail_hmac_len (keyblob : Slice Std.U8) (x : Error)
    (hfit : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length ≤ Std.Usize.max)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = fail x) :
    wrapKeyblob keyblob = fail x := by
  sorry

/-- conditional: if `hmac_sha256` returns a tag `tag` such that the prefix, `keyblob` and `tag`
together are longer than `usize` can hold, then the last append fails and `wrap_keyblob` fails
with a panic. In Rust this is a capacity overflow; the model bound is `Usize.max`.
Hypotheses: those of `wrap_keyblob_ok`, except that the result does not fit. -/
theorem wrap_keyblob_fail_append (hfmt : AllocFmtFormatSpec)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (root : anyhow.Error → ErrRoot) (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (keyblob : Slice Std.U8) (n : Std.Usize)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hcap : km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + n.val ≤ Std.Usize.max)
    (tag : alloc.vec.Vec Std.U8)
    (hover : Std.Usize.max <
      km_compat.KEYBLOB_PREFIX.length + keyblob.val.length + tag.val.length)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY keyblob = ok (.Ok tag)) :
    wrapKeyblob keyblob = fail .panic := by
  sorry

end Keystore2Verify.KmCompat
