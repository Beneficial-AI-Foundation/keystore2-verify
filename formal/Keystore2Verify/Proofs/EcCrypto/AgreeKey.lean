import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- conditional: if the six calls of `agree_key` all return `Ok`, in this order: extract (sender
key, salt), extract (recipient key, first output), `ec_point_oct_to_point other` with `get_point`,
`ecdh_compute_key` (with `version`), extract (secret, second output), expand (32 bytes, info
`aesKeyInfo`), then `agree_key` returns `Ok key`, the output of the last call. Hypotheses: the
shared laws for `from_str_nonconst`, `format` and `context` (`CryptoCtxLaw` at `ZVec` and
`OwnedECPoint`), and the outcomes of the calls and of the `deref` of each vector. -/
theorem agree_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (s3 : Slice Std.U8) (key : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      ok (.Ok key)) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok (.Ok key) := by
  sorry

/-- conditional: under the hypotheses of `agree_key_ok` and the length law
`KeystoreCryptoHkdfExpandSpec`, `agree_key` returns `Ok key` and `key` has 32 bytes. -/
theorem agree_key_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (hlen : KeystoreCryptoHkdfExpandSpec)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (s3 : Slice Std.U8) (key : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      ok (.Ok key)) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Ok key) ∧ ∃ s, zvecDeref key = ok s ∧ s.length = 32 := by
  sorry

/-- conditional: if the first extract returns `Err e`, then `agree_key` returns an error whose root
cause is the crypto error `e`. Hypotheses: the shared laws for `from_str_nonconst`, `format` and
`context`, and the outcomes of the earlier calls and of this one. Later calls are not assumed. -/
theorem agree_key_err_sender_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    
    (e : keystore2_crypto.error.Error)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the first extract returns `Ok` and the second returns `Err e`, then `agree_key`
returns an error whose root cause is `e`. Hypotheses: the shared laws for `from_str_nonconst`,
`format` and `context`, and the outcomes of the earlier calls and of this one. Later calls are not
assumed. -/
theorem agree_key_err_recipient_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (e : keystore2_crypto.error.Error)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if both extracts return `Ok` and `ec_point_oct_to_point other` returns `Err e`,
then `agree_key` returns an error whose root cause is `e`. This is the case of a bad `other`; the
point is parsed only after the two extracts. Hypotheses: the shared laws for `from_str_nonconst`,
`format` and `context`, and the outcomes of the earlier calls and of this one. Later calls are not
assumed. -/
theorem agree_key_err_oct_to_point (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (e : keystore2_crypto.error.Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the earlier calls return `Ok` and `ecdh_compute_key` returns `Err e`, then
`agree_key` returns an error whose root cause is `e`. Hypotheses: the shared laws for
`from_str_nonconst`, `format` and `context`, and the outcomes of the earlier calls and of this one.
Later calls are not assumed. -/
theorem agree_key_err_ecdh (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (e : keystore2_crypto.error.Error)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the earlier calls return `Ok` and the third extract returns `Err e`, then
`agree_key` returns an error whose root cause is `e`. Hypotheses: the shared laws for
`from_str_nonconst`, `format` and `context`, and the outcomes of the earlier calls and of this one.
Later calls are not assumed. -/
theorem agree_key_err_secret_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (e : keystore2_crypto.error.Error)
    (ss s2 : Slice Std.U8) (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the earlier calls return `Ok` and `hkdf_expand` returns `Err e`, then
`agree_key` returns an error whose root cause is `e`. Hypotheses: the shared laws for
`from_str_nonconst`, `format` and `context`, and the outcomes of the earlier calls and of this one.
Later calls are not assumed. -/
theorem agree_key_err_expand (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hp : CryptoCtxLaw root keystore2_crypto.OwnedECPoint)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (ss s2 : Slice Std.U8) (k3 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = ok (.Ok k3))
    (e : keystore2_crypto.error.Error)
    (s3 : Slice Std.U8) (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the first extract panics, then `agree_key` panics in the same way. Hypotheses:
the outcomes of the earlier calls and of this one. No law is needed. -/
theorem agree_key_fail_sender_extract (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    
    (x : Error)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  sorry

/-- conditional: if the first extract returns `Ok` and the second panics, then `agree_key` panics in
the same way. Hypotheses: the outcomes of the earlier calls and of this one. No law is needed. -/
theorem agree_key_fail_recipient_extract (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (x : Error)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  sorry

/-- conditional: if both extracts and the parsing of `other` return `Ok` and `get_point` of the
parsed point panics, then `agree_key` panics in the same way. Hypotheses: the outcomes of the
earlier calls and of this one. No law is needed. -/
theorem agree_key_fail_get_point (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (p : keystore2_crypto.OwnedECPoint) (x : Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  sorry

/-- conditional: if the earlier calls return `Ok` and `ecdh_compute_key` panics, then `agree_key`
panics in the same way. Hypotheses: the outcomes of the earlier calls and of this one. No law is
needed. -/
theorem agree_key_fail_ecdh (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (x : Error)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  sorry

/-- conditional: if the earlier calls return `Ok` and the third extract panics, then `agree_key`
panics in the same way. Hypotheses: the outcomes of the earlier calls and of this one. No law is
needed. -/
theorem agree_key_fail_secret_extract (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (p : keystore2_crypto.OwnedECPoint) (eps : keystore2_crypto_bindgen.ec_point_st)
    (sec : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = ok eps)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = ok (.Ok sec))
    (x : Error)
    (ss s2 : Slice Std.U8) (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  sorry

end Keystore2Verify.EcCrypto
