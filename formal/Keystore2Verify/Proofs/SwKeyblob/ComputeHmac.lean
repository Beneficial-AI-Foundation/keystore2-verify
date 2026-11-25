import Keystore2Verify.Specs.Defs.SwKeyblob

namespace Keystore2Verify.SwKeyblob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `hmac_sha256` returns `Ok tag`
on the key `LEGACY_HMAC_KEY` and the message `data ++ hd`, then `compute_hmac` returns `Ok` of
the first 8 bytes of `tag`. Hypotheses: the two outcomes, `msg` is the bytes `data ++ hd`, and
the law `AllocVecTruncateSpec`. -/
theorem compute_hmac_ok (htrunc : AllocVecTruncateSpec) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (hd tag : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Ok tag)) :
    ∃ t, sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t) ∧
      t.val = tag.val.take 8 := by
  sorry

/-- conditional: under the hypotheses of `compute_hmac_ok` and the law
`KeystoreCryptoHmacSha256Spec`
(an `Ok` tag has 32 bytes), the MAC that `compute_hmac` returns has exactly 8 bytes. -/
theorem compute_hmac_ok_length (htrunc : AllocVecTruncateSpec)
    (hlen : KeystoreCryptoHmacSha256Spec) (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd tag : alloc.vec.Vec Std.U8) (msg : Slice Std.U8)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Ok tag)) :
    ∃ t, sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Ok t) ∧ t.val.length = 8 := by
  sorry

/-- conditional: if `serialize_params hidden` returns `Err e`, then `compute_hmac` returns an
error with the same root cause, and does not call `hmac_sha256`. Hypothesis: the outcome of
`serialize_params`. -/
theorem compute_hmac_err_serialize (root : anyhow.Error → ErrRoot) (data : Slice Std.U8)
    (hidden : Slice KeyParam) (e : anyhow.Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Err e)) :
    ∃ e', sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if `serialize_params hidden` panics, then `compute_hmac` panics in the same
way. Hypothesis: the outcome of `serialize_params`. -/
theorem compute_hmac_fail_serialize (data : Slice Std.U8) (hidden : Slice KeyParam) (x : Error)
    (hser : sw_keyblob.serialize_params hidden = fail x) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail x := by
  sorry

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `hmac_sha256` returns the
crypto error `x` on the message `data ++ hd`, then `compute_hmac` returns an error whose root
cause is `x`. Hypotheses: the two outcomes, `msg` is the bytes `data ++ hd`, and the law
`CryptoFromLaw`. -/
theorem compute_hmac_err_hmac (root : anyhow.Error → ErrRoot) (hfrom : CryptoFromLaw root)
    (data : Slice Std.U8) (hidden : Slice KeyParam) (hd : alloc.vec.Vec Std.U8)
    (msg : Slice Std.U8) (x : keystore2_crypto.error.Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg
      = ok (.Err x)) :
    ∃ e', sw_keyblob.KeyBlob.compute_hmac data hidden = ok (.Err e') ∧
      root e' = ErrRoot.crypto x := by
  sorry

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `hmac_sha256` panics on the
message `data ++ hd`, then `compute_hmac` panics in the same way. Hypotheses: the two outcomes,
and `msg` is the bytes `data ++ hd`. -/
theorem compute_hmac_fail_hmac (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd : alloc.vec.Vec Std.U8) (msg : Slice Std.U8) (x : Error)
    (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hmsg : msg.val = data.val ++ hd.val)
    (hhmac : keystore2_crypto.hmac_sha256 sw_keyblob.KeyBlob.LEGACY_HMAC_KEY msg = fail x) :
    sw_keyblob.KeyBlob.compute_hmac data hidden = fail x := by
  sorry

/-- conditional: if `serialize_params hidden` returns `Ok hd` and `data ++ hd` is longer than the
largest vector, `compute_hmac` panics. Hypotheses: the outcome of `serialize_params`, and the
total length is above `Usize.max`. That is the bound of the Aeneas vector model; in Rust the panic
comes at the lower limit of `isize::MAX` bytes. So this statement describes the model and is not a
capacity guarantee for the Rust code. -/
theorem compute_hmac_fail_capacity (data : Slice Std.U8) (hidden : Slice KeyParam)
    (hd : alloc.vec.Vec Std.U8) (hser : sw_keyblob.serialize_params hidden = ok (.Ok hd))
    (hover : Std.Usize.max < data.val.length + hd.val.length) :
    ∃ x, sw_keyblob.KeyBlob.compute_hmac data hidden = fail x := by
  sorry
end Keystore2Verify.SwKeyblob
