import Keystore2Verify.Specs.Defs.KmCompat

namespace Keystore2Verify.KmCompat
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2.core.slice.Slice renaming starts_with → sliceStartsWith
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming eq → sliceVecEq
open km_compat renaming wrap_keyblob → wrapKeyblob, unwrap_keyblob → unwrapKeyblob

/-- conditional: a blob that does not start with the prefix is `Raw`, unchanged. In the Rust source
this path returns before `HMAC_SHA256_LEN` is read. Hypotheses: the assumption
`CoreSliceStartsWithSpec`, and that the prefix is not a prefix of the blob. -/
theorem unwrap_keyblob_raw_no_prefix (hstart : CoreSliceStartsWithSpec)
    (keyblob : Slice Std.U8) (hpre : ¬ km_compat.KEYBLOB_PREFIX.val <+: keyblob.val) :
    unwrapKeyblob keyblob = ok (.Raw keyblob) := by
  sorry

/-- conditional: a blob that starts with the prefix but has fewer than `n` bytes after it is `Raw`,
unchanged, where `n` is the value of `HMAC_SHA256_LEN`. In the Rust source this path returns
before `hmac_sha256` is called. Hypotheses: the assumption `CoreSliceStartsWithSpec`, that the
prefix is a prefix of the blob, the value `n` of `HMAC_SHA256_LEN`, and that fewer than `n`
bytes follow the prefix. -/
theorem unwrap_keyblob_raw_short (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hshort : (unwrapRest keyblob).length < n.val) :
    unwrapKeyblob keyblob = ok (.Raw keyblob) := by
  sorry

/-- conditional: the blob is wrapped, and `unwrap_keyblob` returns the inner blob (a part of the
input), when the prefix matches, at least `n` bytes follow it, and the last `n` bytes after the
prefix equal the tag that `hmac_sha256` computes over the rest. The inner blob is the bytes
after the prefix without those last `n`. Hypotheses: the assumptions `CoreSliceStartsWithSpec`
and `Shared0SliceEqSpec`; that the prefix is a prefix of the blob; the value `n` of
`HMAC_SHA256_LEN`; the slices `inner` and `want` hold the bytes `unwrapInner` and `unwrapTag`;
the outcome of `hmac_sha256` on `inner`; and that the tag equals `want`. -/
theorem unwrap_keyblob_wrapped (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (heq : Shared0SliceEqSpec) (inner want : Slice Std.U8) (tag : alloc.vec.Vec Std.U8)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hwant : want.val = unwrapTag keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = ok (.Ok tag))
    (htag : want.val = tag.val) :
    unwrapKeyblob keyblob = ok (.Wrapped inner) := by
  sorry

/-- conditional: when the prefix matches and at least `n` bytes follow it but the last `n` bytes
after the prefix differ from the tag that `hmac_sha256` computes, `unwrap_keyblob` returns
`Raw`, unchanged. Hypotheses: as for `unwrap_keyblob_wrapped`, except that the tag differs from
`want`. -/
theorem unwrap_keyblob_raw_tag_differs (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (heq : Shared0SliceEqSpec) (inner want : Slice Std.U8) (tag : alloc.vec.Vec Std.U8)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hwant : want.val = unwrapTag keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = ok (.Ok tag))
    (htag : want.val ≠ tag.val) :
    unwrapKeyblob keyblob = ok (.Raw keyblob) := by
  sorry

/-- conditional: when the prefix matches and at least `n` bytes follow it but `hmac_sha256` returns
an error, `unwrap_keyblob` returns `Raw`, unchanged (the Rust source logs the error first).
Hypotheses: the assumption `CoreSliceStartsWithSpec`; that the prefix is a prefix of the blob; the
value `n` of `HMAC_SHA256_LEN`; that at least `n` bytes follow the prefix; the slice `inner` holds
the bytes `unwrapInner`; the outcome of `hmac_sha256` on `inner`, an error; and the assumptions
`LogLevelPartialCmpSpec`, `LogMaxLevelSpec`, `LogLocSpec` and `LogPrivateApiLogSpec` for the
logging call. -/
theorem unwrap_keyblob_raw_hmac_err (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) (inner : Slice Std.U8)
    (x : keystore2_crypto.error.Error)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = ok (.Err x)) :
    unwrapKeyblob keyblob = ok (.Raw keyblob) := by
  sorry

/-- conditional: when the prefix matches and at least `n` bytes follow it but `hmac_sha256` fails
with `x`, `unwrap_keyblob` fails with `x`. Hypotheses: the assumption
`CoreSliceStartsWithSpec`; that the prefix is a prefix of the blob; the value `n` of
`HMAC_SHA256_LEN`; that at least `n` bytes follow the prefix; the slice `inner` holds the bytes
`unwrapInner`; and the outcome of `hmac_sha256` on `inner`, a failure. -/
theorem unwrap_keyblob_fail_hmac (hstart : CoreSliceStartsWithSpec) (keyblob : Slice Std.U8)
    (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val)
    (n : Std.Usize) (hn : keystore2_crypto.HMAC_SHA256_LEN = ok n)
    (hlen : n.val ≤ (unwrapRest keyblob).length)
    (inner : Slice Std.U8) (x : Error)
    (hinner : inner.val = unwrapInner keyblob n.val)
    (hmac : keystore2_crypto.hmac_sha256 km_compat.KEYBLOB_HMAC_KEY inner = fail x) :
    unwrapKeyblob keyblob = fail x := by
  sorry

/-- conditional: if the prefix matches and `HMAC_SHA256_LEN` fails with `x`, then `unwrap_keyblob`
fails with `x`. Hypotheses: the assumption `CoreSliceStartsWithSpec`, that the prefix is a prefix
of the blob, and the outcome of `HMAC_SHA256_LEN`. -/
theorem unwrap_keyblob_fail_hmac_len (hstart : CoreSliceStartsWithSpec)
    (keyblob : Slice Std.U8) (hpre : km_compat.KEYBLOB_PREFIX.val <+: keyblob.val) (x : Error)
    (hn : keystore2_crypto.HMAC_SHA256_LEN = fail x) :
    unwrapKeyblob keyblob = fail x := by
  sorry

end Keystore2Verify.KmCompat
