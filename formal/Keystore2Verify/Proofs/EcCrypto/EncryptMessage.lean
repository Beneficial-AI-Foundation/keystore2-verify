import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.vec

/-- conditional: if `generate`, `public_key`, `generate_salt`, `agree_key` and `aes_gcm_encrypt` all
return `Ok`, in this order, then `encrypt_message` returns `Ok (spk, salt, iv, ciphertext, tag)`:
the sender public key, the salt, the IV, the ciphertext and the tag. The key derivation uses the
salt, the recipient key as the other key, `spk` as the sender key, the recipient key again as the
recipient key, and the version `Current`. Hypotheses: the shared laws for `from_str_nonconst`,
`format` and `context` (at the five calls of lines 82, 83, 84, 93 and 95), and the outcomes of the
calls. -/
theorem encrypt_message_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8) (ct iv tag : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = ok (.Ok (ct, iv, tag))) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok
    (.Ok (spk, salt, iv, ct, tag)) := by
  sorry

/-- conditional: under the hypotheses of `encrypt_message_ok` and the length laws
`KeystoreCryptoGenerateSaltSpec` and `AesGcmEncryptSpec`, the result of `encrypt_message` has a salt
of 16 bytes, an IV of 12 bytes, a tag of 16 bytes and a ciphertext as long as `message`. -/
theorem encrypt_message_ok_lengths (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (hsalt : KeystoreCryptoGenerateSaltSpec) (haes : AesGcmEncryptSpec)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (ks : Slice Std.U8) (ct iv tag : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = ok (.Ok (ct, iv, tag))) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message =
      ok (.Ok (spk, salt, iv, ct, tag)) ∧
      salt.val.length = 16 ∧ iv.val.length = 12 ∧ tag.val.length = 16 ∧
      ct.val.length = message.length := by
  sorry

/-- conditional: if `encrypt_message` returns `Ok (spk, salt, iv, ct, tag)`, then `spk` has between
1 and 133 bytes, `salt` has 16 bytes, `iv` has 12 bytes, `tag` has 16 bytes and `ct` is as long as
`message`. The hypothesis is the returned value; the outcomes of the calls inside are not assumed.
Hypotheses: the `context` laws `AnyCtxLaw` at line 83 and `CryptoCtxLaw` at line 95, the
vector-valued `CryptoCtxLaw`, which covers both the salt `context` (line 84) and the `context`
inside `public_key` (these laws let an `Ok` after `context` come only from an `Ok` before it), the
length laws `EcPointPointToOctSpec`, `KeystoreCryptoGenerateSaltSpec` and `AesGcmEncryptSpec`, and
the returned value. -/
theorem encrypt_message_ok_lengths_of_result (root : anyhow.Error → ErrRoot)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (hoct : EcPointPointToOctSpec) (hsalt : KeystoreCryptoGenerateSaltSpec)
    (haes : AesGcmEncryptSpec)
    (recipient message : Slice Std.U8)
    (spk salt iv ct tag : alloc.vec.Vec Std.U8)
    (h : ec_crypto.ECDHPrivateKey.encrypt_message recipient message =
      ok (.Ok (spk, salt, iv, ct, tag))) :
    (1 ≤ spk.val.length ∧ spk.val.length ≤ 133) ∧
      salt.val.length = 16 ∧ iv.val.length = 12 ∧ tag.val.length = 16 ∧
      ct.val.length = message.length := by
  sorry

/-- conditional: if `generate` returns `Err e`, then `encrypt_message` returns an error with the
same root cause as `e`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the
`context` law at line 82, and the outcome of `generate`. In the Rust source the `?` of line 82
returns at this point, before `public_key` is called, so the statement takes no law for the later
calls. -/
theorem encrypt_message_err_generate (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (recipient message : Slice Std.U8)
    (e : anyhow.Error)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if `generate` returns `Ok` and `public_key` returns `Err e`, then `encrypt_message`
returns an error with the same root cause as `e`. Hypotheses: the shared laws for
`from_str_nonconst` and `format`, the `context` laws at lines 82 and 83, and the outcomes of the two
calls. In the Rust source the `?` of line 83 returns at this point, before `generate_salt` is
called. -/
theorem encrypt_message_err_public_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (e : anyhow.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if `generate` and `public_key` return `Ok` and `generate_salt` returns `Err e`,
then `encrypt_message` returns an error whose root cause is the crypto error `e`. Hypotheses: the
shared laws for `from_str_nonconst` and `format`, the `context` laws at lines 82, 83 and 84, and the
outcomes of the three calls. In the Rust source the `?` of line 84 returns at this point, before
`agree_key` is called. -/
theorem encrypt_message_err_generate_salt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (e : keystore2_crypto.error.Error)
    (hs : keystore2_crypto.generate_salt = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if the first three steps return `Ok` and `agree_key` returns `Err e`, then
`encrypt_message` returns an error with the same root cause as `e`. The statement assumes only that
`agree_key` returned `Err e`. In the Rust source `agree_key` returns an error when
`recipient_public_key` does not decode, and the `?` of line 93 returns at this point, before
`aes_gcm_encrypt` is called. Hypotheses: the shared laws for `from_str_nonconst` and
`format`, the `context` laws at lines 82, 83, 84 and 93, and the outcomes of the calls. -/
theorem encrypt_message_err_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (e : anyhow.Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = root e := by
  sorry

/-- conditional: if the first four steps return `Ok` and `aes_gcm_encrypt` returns `Err e`, then
`encrypt_message` returns an error whose root cause is the crypto error `e`. Hypotheses: the shared
laws for `from_str_nonconst` and `format`, the `context` laws at the five calls of lines 82, 83, 84,
93 and 95, and the outcomes of the calls. -/
theorem encrypt_message_err_aes_gcm_encrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (hc95 : CryptoCtxLaw root
      (alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (e : keystore2_crypto.error.Error)
    (ks : Slice Std.U8)
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.encrypt_message recipient message = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if `generate` returns `Ok` and `public_key` fails, then `encrypt_message` returns
the same `fail x`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context`
law at line 82, and the outcomes of `generate` and `public_key`. -/
theorem encrypt_message_fail_public_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (x : Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x := by
  sorry

/-- conditional: if the first three steps return `Ok` and `agree_key` fails, then `encrypt_message`
returns the same `fail x`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the
`context` laws at lines 82, 83 and 84, and the outcomes of the earlier calls and of this one. -/
theorem encrypt_message_fail_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (x : Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x := by
  sorry

/-- conditional: if `generate` fails, then `encrypt_message` returns the same `fail x`. Hypothesis:
the outcome of this call. No law is needed. -/
theorem encrypt_message_fail_generate (recipient message : Slice Std.U8)
    (x : Error)
    (hg : ec_crypto.ECDHPrivateKey.generate = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x := by
  sorry
/-- conditional: if `generate` and `public_key` return `Ok` and `generate_salt` fails, then
`encrypt_message` returns the same `fail x`. Hypotheses: the shared laws for `from_str_nonconst` and
`format`, the `context` laws at lines 82 and 83, and the outcomes of the earlier calls and of this
one. -/
theorem encrypt_message_fail_generate_salt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (x : Error)
    (hs : keystore2_crypto.generate_salt = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x := by
  sorry
/-- conditional: if `deref` of the derived key fails, then `encrypt_message` returns the same
`fail x`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` laws at
lines 82, 83, 84 and 93, and the outcomes of the earlier calls and of this one. -/
theorem encrypt_message_fail_deref_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (x : Error)
    (hd : zvecDeref key = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x := by
  sorry
/-- conditional: if `aes_gcm_encrypt` fails, then `encrypt_message` returns the same `fail x`.
Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` laws at lines 82,
83, 84 and 93, and the outcomes of the earlier calls and of this one. -/
theorem encrypt_message_fail_aes_gcm_encrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc82 : AnyCtxLaw root ec_crypto.ECDHPrivateKey)
    (hc83 : AnyCtxLaw root (alloc.vec.Vec Std.U8))
    (hc84 : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (hc93 : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (recipient message : Slice Std.U8)
    (k : ec_crypto.ECDHPrivateKey)
    (spk : alloc.vec.Vec Std.U8)
    (salt : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hg : ec_crypto.ECDHPrivateKey.generate = ok (.Ok k))
    (hpk : ec_crypto.ECDHPrivateKey.public_key k = ok (.Ok spk))
    (hs : keystore2_crypto.generate_salt = ok (.Ok salt))
    (ha : ec_crypto.ECDHPrivateKey.agree_key k (Vec.deref salt) recipient
      (Vec.deref spk) recipient keystore2_crypto.EcdhComputeKeyVersion.Current =
      ok (.Ok key))
    (ks : Slice Std.U8) (x : Error)
    (hd : zvecDeref key = ok ks)
    (he : keystore2_crypto.aes_gcm_encrypt message ks = fail x) :
    ec_crypto.ECDHPrivateKey.encrypt_message recipient message = fail x := by
  sorry

end Keystore2Verify.EcCrypto
