import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.vec
open ec_crypto.ECDHPrivateKey.decrypt_message
open closure.Insts.CoreOpsFunctionFnOnceTupleErrorResultZVecError renaming
  call_once → closureCallOnce

/-- conditional: if `public_key`, `agree_key` (version `Current`) and the first `aes_gcm_decrypt`
return `Ok`, then `decrypt_message` returns `Ok p`, the plaintext of that decryption. The legacy key
is not derived. Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context`
(`AnyCtxLaw` at the lines 117 and 129, `CryptoCtxLaw` at line 131), and the outcomes of the calls.
-/
theorem decrypt_message_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (p : keystore2_crypto.zvec.ZVec)
    (hdec : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Ok p)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Ok p) := by
  sorry

/-- conditional: under the hypotheses of `decrypt_message_ok` and the length law
`AesGcmDecryptSpec`, the plaintext returned by `decrypt_message` is as long as `ct`. -/
theorem decrypt_message_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (hlen : AesGcmDecryptSpec)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (p : keystore2_crypto.zvec.ZVec)
    (hdec : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Ok p)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Ok p) ∧ ∃ s, zvecDeref p = ok s ∧ s.length = ct.length := by
  sorry

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1`, whatever `e1` is, the legacy key
(version `LegacyTruncated`) is derived from the same arguments, and the second `aes_gcm_decrypt`
with it returns `Ok p`, then `decrypt_message` returns `Ok p`. Hypotheses: the shared laws for
`from_str_nonconst`, `format` and `context` (`AnyCtxLaw` at the lines 117 and 129, `CryptoCtxLaw` at
line 131), and the outcomes of the calls. -/
theorem decrypt_message_ok_legacy (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (ks2 : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok
      (.Ok key2))
    (hd2 : zvecDeref key2 = ok ks2)
    (p : keystore2_crypto.zvec.ZVec)
    (hdec2 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks2 = ok (.Ok p)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Ok p) := by
  sorry

/-- conditional: if `public_key` returns `Err e`, then `decrypt_message` returns an error with the
same root cause as `e`, and nothing else is called. Hypothesis: the outcome of the call. No law is
needed. -/
theorem decrypt_message_err_public_key (root : anyhow.Error → ErrRoot)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (e : anyhow.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if `public_key` returns `Ok` and `agree_key` (version `Current`) returns `Err e`,
then `decrypt_message` returns an error with the same root cause as `e`, and no decryption is tried.
A bad or empty `sender` ends here. Hypotheses: the shared laws for `from_str_nonconst`, `format` and
`context` (`AnyCtxLaw` at the lines 117 and 129, `CryptoCtxLaw` at line 131), and the outcomes of
the calls. -/
theorem decrypt_message_err_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (e : anyhow.Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1`, and the legacy `agree_key` returns
`Err e`, then `decrypt_message` returns an error with the same root cause as `e`. The first error
`e1` does not matter. Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context`
(`AnyCtxLaw` at the lines 117 and 129, `CryptoCtxLaw` at line 131), and the outcomes of the calls.
-/
theorem decrypt_message_err_legacy_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (e : anyhow.Error)
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok
      (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1` and the second one, with the legacy
key, returns `Err e`, then `decrypt_message` returns an error whose root cause is the crypto error
`e` of the second call. The first error `e1` is dropped, whatever it is. Hypotheses: the shared laws
for `from_str_nonconst`, `format` and `context` (`AnyCtxLaw` at the lines 117 and 129,
`CryptoCtxLaw` at line 131), and the outcomes of the calls. -/
theorem decrypt_message_err_legacy_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (ks2 : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok
      (.Ok key2))
    (hd2 : zvecDeref key2 = ok ks2)
    (e : keystore2_crypto.error.Error)
    (hdec2 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks2 = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if `public_key` panics, then `decrypt_message` panics in the same way. Hypothesis:
the outcome of the call. No law is needed. -/
theorem decrypt_message_fail_public_key (self : ec_crypto.ECDHPrivateKey)
    (sender salt iv ct tag : Slice Std.U8)
    (x : Error) (hpk : ec_crypto.ECDHPrivateKey.public_key self = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry

/-- conditional: if `public_key` returns `Ok` and `agree_key` (version `Current`) panics, then
`decrypt_message` panics in the same way. Hypotheses: the outcomes of the two calls. No law is
needed. -/
theorem decrypt_message_fail_agree_key (self : ec_crypto.ECDHPrivateKey)
    (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8) (x : Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1` and the legacy `agree_key` panics,
then `decrypt_message` panics in the same way. Hypotheses: the shared laws for `from_str_nonconst`,
`format` and `context` (`AnyCtxLaw` at the lines 117 and 129, `CryptoCtxLaw` at line 131), and the
outcomes of the calls. -/
theorem decrypt_message_fail_legacy_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (x : Error)
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry

/-- exact: the fallback closure of `decrypt_message` does not look at the error of the first
decryption. Its result is the same for every error value. -/
theorem decrypt_message_closure_ignores_error
    (c : closure)
    (e1 e2 : keystore2_crypto.error.Error) :
    closureCallOnce c e1 = closureCallOnce c e2 := by
  sorry

/-- conditional: if `deref` of the derived key panics, then `decrypt_message` panics in the same
way. Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context` (the steps before
it pass through `context`), and the outcomes of the earlier calls and of this one. -/
theorem decrypt_message_fail_deref_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (x : Error)
    (hd : zvecDeref key = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry
/-- conditional: if the first `aes_gcm_decrypt` panics, then `decrypt_message` panics in the same
way. The legacy key is not derived and no second decryption is tried: the panic is not an `Err`, so
the fallback does not run. Hypotheses: the shared laws for `from_str_nonconst`, `format` and
`context` (the steps before it pass through `context`), and the outcomes of the earlier calls and of
this one. -/
theorem decrypt_message_fail_first_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (x : Error)
    (hdec : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry
/-- conditional: if `deref` of the legacy key panics, then `decrypt_message` panics in the same way.
Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context` (the steps before it
pass through `context`), and the outcomes of the earlier calls and of this one. -/
theorem decrypt_message_fail_deref_legacy_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok (.Ok key2))
    (x : Error)
    (hd2 : zvecDeref key2 = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry
/-- conditional: if the second `aes_gcm_decrypt`, with the legacy key panics, then `decrypt_message`
panics in the same way. Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context`
(the steps before it pass through `context`), and the outcomes of the earlier calls and of this
one. -/
theorem decrypt_message_fail_legacy_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8)
    (e1 : keystore2_crypto.error.Error)
    (key2 : keystore2_crypto.zvec.ZVec)
    (ks2 : Slice Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (hdec1 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks = ok (.Err e1))
    (ha2 : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.LegacyTruncated = ok (.Ok key2))
    (hd2 : zvecDeref key2 = ok ks2)
    (x : Error)
    (hdec2 : keystore2_crypto.aes_gcm_decrypt ct iv tag ks2 = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  sorry

end Keystore2Verify.EcCrypto
