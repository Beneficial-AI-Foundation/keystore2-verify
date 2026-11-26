import Keystore2Verify.Specs.Defs.EcCrypto
import Keystore2Verify.Proofs.Lemmas.BootLevelKeysBind

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.result.Result.Insts.CoreOpsTry renaming branch → resultBranch
open core.result.Result.Insts.CoreOpsTry_traitFromResidualResult renaming
  from_residual → resultFromResidual

/-! The three cases where a successful HKDF extract is followed by a failing view of that
result describe the unconstrained extraction only. `HkdfExtractLenLaw` requires that same view
to succeed, so none of the three cases is a path under the length law. -/

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨a5, h5⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:70: hkdf_extract on secret failed")
  obtain ⟨a6, h6⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:73: hkdf_expand failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  obtain ⟨t5, g5⟩ := hfmt a5
  obtain ⟨t6, g6⟩ := hfmt a6
  have hz1 := hz.1
  have hp1 := hp.1
  unfold aesKeyInfo at hexp
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hext3, hd3, hexp, hz1, hp1, lift, h1, g1,
    h2, g2, h3, g3, h4, g4, h5, g5, h6, g6, core.hint.must_use,
    resultBranch]

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
  refine ⟨agree_key_ok root hargs hfmt hz hp self salt other sender recipient version k1 s1 k2 p
    eps sec ss s2 k3 s3 key hext1 hd1 hext2 hoct hgp hecdh hds hd2 hext3 hd3 hexp, ?_⟩
  obtain ⟨s, hs, hl⟩ := hlen _ _ _ _ hexp
  exact ⟨s, hs, by simpa [keystore2_crypto.AES_256_KEY_LENGTH] using hl⟩

/-- conditional: if the first extract returns `Err e`, then `agree_key` returns an error whose root
cause is the crypto error `e`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the
`context` law `CryptoCtxLaw` at `ZVec`, and the outcome of this call. In the Rust source the `?` of
line 63 returns at this point, before the second extract is called. -/
theorem agree_key_err_sender_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (e : keystore2_crypto.error.Error)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = ok
    (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨e', hc, hr⟩ := hz.2 e t1
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hc, resultFromResidual,
    h1, g1, core.hint.must_use, resultBranch]

/-- conditional: if the first extract returns `Ok` and the second returns `Err e`, then `agree_key`
returns an error whose root cause is `e`. Hypotheses: the shared laws for `from_str_nonconst` and
`format`, the `context` law `CryptoCtxLaw` at `ZVec`, and the outcomes of the two calls and of the
`deref` of the first output. In the Rust source the `?` of line 65 returns at this point, before the
point is parsed. -/
theorem agree_key_err_recipient_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  have hz1 := hz.1
  obtain ⟨e', hc, hr⟩ := hz.2 e t2
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hz1, hc,
    resultFromResidual, h1, g1, h2, g2,
    core.hint.must_use, resultBranch]

/-- conditional: if both extracts return `Ok` and `ec_point_oct_to_point other` returns `Err e`,
then `agree_key` returns an error whose root cause is `e`. The statement assumes only that
`ec_point_oct_to_point other` returned `Err e`. In the Rust source `agree_key` returns an error
when `other` does not decode, and the point is parsed after the two extracts. Hypotheses: the
shared laws for `from_str_nonconst` and `format`, the `context` laws `CryptoCtxLaw` at `ZVec` and
`OwnedECPoint`, and the outcomes of the earlier calls and of this one. Later calls are not
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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  have hz1 := hz.1
  obtain ⟨e', hc, hr⟩ := hp.2 e t3
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hz1, hc,
    resultFromResidual, h1, g1, h2, g2,
    h3, g3, core.hint.must_use, resultBranch]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  have hz1 := hz.1
  have hp1 := hp.1
  obtain ⟨e', hc, hr⟩ := hz.2 e t4
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hz1, hp1, hc,
    resultFromResidual, h1, g1, h2, g2,
    h3, g3, h4, g4, core.hint.must_use, resultBranch]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨a5, h5⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:70: hkdf_extract on secret failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  obtain ⟨t5, g5⟩ := hfmt a5
  have hz1 := hz.1
  have hp1 := hp.1
  obtain ⟨e', hc, hr⟩ := hz.2 e t5
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hext3, hz1, hp1, hc,
    resultFromResidual, h1, g1, h2, g2,
    h3, g3, h4, g4, h5, g5, core.hint.must_use, resultBranch]

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
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨a5, h5⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:70: hkdf_extract on secret failed")
  obtain ⟨a6, h6⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:73: hkdf_expand failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  obtain ⟨t5, g5⟩ := hfmt a5
  obtain ⟨t6, g6⟩ := hfmt a6
  have hz1 := hz.1
  have hp1 := hp.1
  obtain ⟨e', hc, hr⟩ := hz.2 e t6
  refine ⟨e', ?_, hr⟩
  unfold aesKeyInfo at hexp
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hext3, hd3, hexp, hz1, hp1, hc,
    resultFromResidual, lift, h1, g1, h2,
    g2, h3, g3, h4, g4, h5, g5, h6, g6, core.hint.must_use,
    resultBranch]

/-- conditional: if the first extract fails, then `agree_key` returns the same `fail x`.
Hypothesis: the outcome of this call. No law is needed. -/
theorem agree_key_fail_sender_extract (self : ec_crypto.ECDHPrivateKey)
    (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (x : Error)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, core.hint.must_use, resultBranch]

/-- conditional: if `deref` of the output of the first extract (the first call is `Ok`) fails, then
`agree_key` returns the same `fail x`. Hypotheses: the shared laws for `from_str_nonconst` and
`format`, the `context` law `CryptoCtxLaw` at `ZVec` (the first call passes through `context`), and
the outcomes of the first call and of this one. -/
theorem agree_key_fail_deref_sender_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (x : Error)
    (hd1 : zvecDeref k1 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  have hz1 := hz.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hz1, h1, g1, core.hint.must_use, resultBranch]

/-- conditional: if the second extract fails, then `agree_key` returns the same `fail x`.
Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` law `CryptoCtxLaw`
at `ZVec` (the first call passes through `context`), and the outcomes of the earlier calls and of
this one. -/
theorem agree_key_fail_recipient_extract (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (x : Error)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  have hz1 := hz.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hz1, h1, g1, core.hint.must_use,
    resultBranch]

/-- conditional: if `ec_point_oct_to_point other` fails, then `agree_key` returns the same
`fail x`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` law
`CryptoCtxLaw` at `ZVec` (the two extracts pass through `context`), and the outcomes of the earlier
calls and of this one. -/
theorem agree_key_fail_oct_to_point (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion)
    (k1 : keystore2_crypto.zvec.ZVec)
    (s1 : Slice Std.U8)
    (k2 : keystore2_crypto.zvec.ZVec)
    (hext1 : keystore2_crypto.hkdf_extract sender salt = ok (.Ok k1))
    (hd1 : zvecDeref k1 = ok s1)
    (hext2 : keystore2_crypto.hkdf_extract recipient s1 = ok (.Ok k2))
    (x : Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  have hz1 := hz.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hz1, h1, g1, h2, g2, core.hint.must_use,
    resultBranch]

/-- conditional: if `get_point` of the parsed point fails, then `agree_key` returns the same
`fail x`. Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context`, and the
outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_get_point (root : anyhow.Error → ErrRoot)
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
    (p : keystore2_crypto.OwnedECPoint) (x : Error)
    (hoct : keystore2_crypto.ec_point_oct_to_point other = ok (.Ok p))
    (hgp : keystore2_crypto.OwnedECPoint.get_point p = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  have hz1 := hz.1
  have hp1 := hp.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hz1, hp1, h1, g1, h2, g2, h3, g3, core.hint.must_use,
    resultBranch]

/-- conditional: if `ecdh_compute_key` fails, then `agree_key` returns the same `fail x`.
Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context` (the calls before it
pass through `context`), and the outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_ecdh (root : anyhow.Error → ErrRoot)
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
    (x : Error)
    (hecdh : keystore2_crypto.ecdh_compute_key eps self version = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  have hz1 := hz.1
  have hp1 := hp.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hz1, hp1, h1, g1, h2, g2, h3, g3,
    core.hint.must_use, resultBranch]

/-- conditional: if `deref` of the ECDH secret fails, then `agree_key` returns the same `fail x`.
Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context` (the calls before it
pass through `context`), and the outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_deref_secret (root : anyhow.Error → ErrRoot)
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
    (x : Error)
    (hds : zvecDeref sec = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  have hz1 := hz.1
  have hp1 := hp.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hz1, hp1, h1, g1, h2, g2, h3, g3, h4, g4,
    core.hint.must_use, resultBranch]

/-- conditional: if `deref` of the output of the second extract (the `deref` of the secret is `Ok`)
fails, then `agree_key` returns the same `fail x`. Hypotheses: the shared laws for
`from_str_nonconst`, `format` and `context` (the calls before it pass through `context`), and the
outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_deref_recipient_prk (root : anyhow.Error → ErrRoot)
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
    (ss : Slice Std.U8) (x : Error)
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  have hz1 := hz.1
  have hp1 := hp.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hz1, hp1, h1, g1, h2, g2, h3, g3, h4, g4,
    core.hint.must_use, resultBranch]

/-- conditional: if the third extract fails, then `agree_key` returns the same `fail x`.
Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context` (the calls before it
pass through `context`), and the outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_secret_extract (root : anyhow.Error → ErrRoot)
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
    (ss s2 : Slice Std.U8) (x : Error)
    (hds : zvecDeref sec = ok ss) (hd2 : zvecDeref k2 = ok s2)
    (hext3 : keystore2_crypto.hkdf_extract ss s2 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  have hz1 := hz.1
  have hp1 := hp.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hext3, hz1, hp1, h1, g1, h2, g2, h3, g3,
    h4, g4, core.hint.must_use, resultBranch]

/-- conditional: if `deref` of the output of the third extract fails, then `agree_key` returns the
same `fail x`. Hypotheses: the shared laws for `from_str_nonconst`, `format` and `context` (the
calls before it pass through `context`), and the outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_deref_prk (root : anyhow.Error → ErrRoot)
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
    (x : Error)
    (hd3 : zvecDeref k3 = fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨a5, h5⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:70: hkdf_extract on secret failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  obtain ⟨t5, g5⟩ := hfmt a5
  have hz1 := hz.1
  have hp1 := hp.1
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hext3, hd3, hz1, hp1, h1, g1, h2, g2, h3,
    g3, h4, g4, h5, g5, core.hint.must_use, resultBranch]

/-- conditional: if `hkdf_expand` fails, then `agree_key` returns the same `fail x`. Hypotheses:
the shared laws for `from_str_nonconst`, `format` and `context` (the calls before it pass through
`context`), and the outcomes of the earlier calls and of this one. -/
theorem agree_key_fail_expand (root : anyhow.Error → ErrRoot)
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
    (s3 : Slice Std.U8) (x : Error)
    (hd3 : zvecDeref k3 = ok s3)
    (hexp : keystore2_crypto.hkdf_expand keystore2_crypto.AES_256_KEY_LENGTH s3 aesKeyInfo =
      fail x) :
    ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version = fail x := by
  obtain ⟨a1, h1⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:63: hkdf_extract on sender_public_key failed")
  obtain ⟨a2, h2⟩ :=
    hargs (toStr "keystore2/src/ec_crypto.rs:65: hkdf_extract on recipient_public_key failed")
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:67: ec_point_oct_to_point failed")
  obtain ⟨a4, h4⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:69: ecdh_compute_key failed")
  obtain ⟨a5, h5⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:70: hkdf_extract on secret failed")
  obtain ⟨t1, g1⟩ := hfmt a1
  obtain ⟨t2, g2⟩ := hfmt a2
  obtain ⟨t3, g3⟩ := hfmt a3
  obtain ⟨t4, g4⟩ := hfmt a4
  obtain ⟨t5, g5⟩ := hfmt a5
  have hz1 := hz.1
  have hp1 := hp.1
  unfold aesKeyInfo at hexp
  unfold ec_crypto.ECDHPrivateKey.agree_key
  simp [hext1, hd1, hext2, hoct, hgp, hecdh, hds, hd2, hext3, hd3, hexp, hz1, hp1, lift, h1, g1,
    h2, g2, h3, g3, h4, g4, h5, g5, core.hint.must_use,
    resultBranch]


/-- A `context` call that returns `ok c'` on `r` either keeps an `Ok` or turns an `Err` into an
`Err`. -/
private theorem ctx_cases {T E Er C : Type} {rootE : E → ErrRoot} {root : Er → ErrRoot}
    {ctx : core.result.Result T E → C → Result (core.result.Result T Er)}
    (hl : ResultContextLaw rootE root ctx) (r : core.result.Result T E) (c : C)
    (c' : core.result.Result T Er) (h : ctx r c = ok c') :
    (∃ v, r = .Ok v ∧ c' = .Ok v) ∨ (∃ e e', r = .Err e ∧ c' = .Err e') := by
  cases r with
  | Ok v => left; rw [hl.1 v c] at h; simp only [ok.injEq] at h; subst h; exact ⟨v, rfl, rfl⟩
  | Err e =>
    right
    obtain ⟨e', h1, _⟩ := hl.2 e c
    rw [h1] at h; simp only [ok.injEq] at h; subst h; exact ⟨e, _, rfl, rfl⟩

/-- Only the final expand and its context determine the length of an observed success. -/
theorem agree_key_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hz : CryptoCtxLaw root keystore2_crypto.zvec.ZVec) (hlen : KeystoreCryptoHkdfExpandSpec)
    (self : ec_crypto.ECDHPrivateKey) (salt other sender recipient : Slice Std.U8)
    (version : keystore2_crypto.EcdhComputeKeyVersion) (key : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.agree_key self salt other sender recipient version =
      ok (.Ok key)) : ∃ s, zvecDeref key = ok s ∧ s.length = 32 := by
  unfold ec_crypto.ECDHPrivateKey.agree_key at h
  simp only [Keystore2Verify.BootLevelKeys.bind_eq_ok_iff, core.hint.must_use,
    resultBranch, ok.injEq, exists_eq_left'] at h
  obtain ⟨r, hr, a, ha, t, ht, c, hc, cf, hcf, h⟩ := h
  rcases c with v | e
  swap
  · simp at hcf; subst hcf
    simp [resultFromResidual] at h
  simp at hcf; subst hcf
  simp only [Keystore2Verify.BootLevelKeys.bind_eq_ok_iff, ok.injEq,
    exists_eq_left'] at h
  obtain ⟨s2, hd1, r2, hr2, a2, ha2, t2, ht2, c2, hc2, cf2, hcf2, h⟩ := h
  rcases c2 with v | e
  swap
  · simp at hcf2; subst hcf2
    simp [resultFromResidual] at h
  simp at hcf2; subst hcf2
  simp only [Keystore2Verify.BootLevelKeys.bind_eq_ok_iff, ok.injEq,
    exists_eq_left'] at h
  obtain ⟨r4, hr4, a3, ha3, t3, ht3, c3, hc3, cf3, hcf3, h⟩ := h
  rcases c3 with v | e
  swap
  · simp at hcf3; subst hcf3
    simp [resultFromResidual] at h
  simp at hcf3; subst hcf3
  simp only [Keystore2Verify.BootLevelKeys.bind_eq_ok_iff, ok.injEq,
    exists_eq_left'] at h
  obtain ⟨eps, hg, r6, hr6, a4, ha4, t4, ht4, c4, hc4, cf4, hcf4, h⟩ := h
  rcases c4 with v | e
  swap
  · simp at hcf4; subst hcf4
    simp [resultFromResidual] at h
  simp at hcf4; subst hcf4
  simp only [Keystore2Verify.BootLevelKeys.bind_eq_ok_iff, ok.injEq,
    exists_eq_left'] at h
  obtain ⟨s9, hd4, s10, hd5, r8, hr8, a5, ha5, t5, ht5, c5, hc5, cf5, hcf5, h⟩ := h
  rcases c5 with v | e
  swap
  · simp at hcf5; subst hcf5
    simp [resultFromResidual] at h
  simp at hcf5; subst hcf5
  simp only [Keystore2Verify.BootLevelKeys.bind_eq_ok_iff, ok.injEq,
    exists_eq_left'] at h
  obtain ⟨s13, hd6, s14, hl14, r10, hr10, a6, ha6, t6, ht6, c6, hc6, cf6, hcf6, h⟩ := h
  rcases ctx_cases hz _ _ _ hc6 with ⟨v6, rfl, rfl⟩ | ⟨e, e', rfl, rfl⟩
  swap
  · simp at hcf6; subst hcf6
    simp [resultFromResidual] at h
  simp at hcf6; subst hcf6
  simp at h; subst h
  obtain ⟨s, hs, hl⟩ := hlen _ _ _ _ hr10
  exact ⟨s, hs, by simpa [keystore2_crypto.AES_256_KEY_LENGTH] using hl⟩

end Keystore2Verify.EcCrypto
