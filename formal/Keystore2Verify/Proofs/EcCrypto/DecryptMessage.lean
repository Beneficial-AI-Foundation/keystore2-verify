import Keystore2Verify.Specs.Defs.EcCrypto

/-!
# Statements about `ECDHPrivateKey::decrypt_message`

`decrypt_message` derives the AES key with `agree_key` (version `Current`) and decrypts. If the
decryption returns an `Err`, the closure of `or_else` derives a second key (version
`LegacyTruncated`) and decrypts again.

In the Lean model every external call is a pure function, so two calls with equal arguments are one
value. In the Rust source each call of `agree_key` runs `hkdf_extract` on the sender key and on the
recipient key and parses the point of `other_public_key` before it uses the version, and each such
call allocates a new secret vector (`ZVec::new`, `mlock`). The second call can therefore fail at a
step that the first call passed. The theorems about the fallback cover a legacy error at a step that
depends on the version (`ecdh_compute_key` and the steps after it). A run in which one of the shared
steps (the two `hkdf_extract` calls and the point conversion) gives different outcomes in the two
attempts is outside the model. The same holds for the two `aes_gcm_decrypt` calls: if the two keys
are equal slices, the model makes the two decryptions one value, so a statement that assumes `Err`
for the first and `Ok` for the second has no instance for equal keys. The statements do not force
the keys to be equal.
-/

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.vec
open core.result.Result.Insts core.convert core.result
open ec_crypto.ECDHPrivateKey.decrypt_message
open closure.Insts.CoreOpsFunctionFnOnceTupleErrorResultZVecError renaming
  call_once → closureCallOnce

/-- Peel the first step off a successful `do` block: the bound computation succeeded. -/
private theorem dec_bind_ok {α β : Type} {c : Result α} {f : α → Result β} {y : β}
    (h : (do let a ← c; f a) = ok y) : ∃ a, c = ok a ∧ f a = ok y := by
  cases c with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis i k => simp at h
  | div => simp at h

/-- A `context` call that satisfies the law and returns `Ok v` was given `Ok v`. -/
private theorem dec_ctx_ok_of {T E Er C : Type} {rE : E → ErrRoot} {rt : Er → ErrRoot}
    {ctx : core.result.Result T E → C → Result (core.result.Result T Er)}
    (hl : ResultContextLaw rE rt ctx) (r : core.result.Result T E) (c : C) (v : T)
    (h : ctx r c = ok (.Ok v)) : r = .Ok v := by
  cases r with
  | Ok v' => rw [hl.1] at h; simp at h; rw [h]
  | Err x => obtain ⟨e, he, -⟩ := hl.2 x c; rw [he] at h; simp at h

/-- conditional: if `public_key`, `agree_key` (version `Current`) and the first `aes_gcm_decrypt`
return `Ok`, then `decrypt_message` returns `Ok p`, the plaintext of that decryption. In the Rust
source `or_else` does not call its closure when the decryption returns `Ok`, so the statement takes
no law for the closure. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the
`context` law `AnyCtxLaw` at line 117, and the outcomes of the calls. -/
theorem decrypt_message_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec, h1, f1, hc.1,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: under the hypotheses of `decrypt_message_ok` and the length law
`AesGcmDecryptSpec`, the plaintext returned by `decrypt_message` is as long as `ct`. This statement
starts from a successful first attempt; `decrypt_message_ok_length_of_result` starts from the
returned value. -/
theorem decrypt_message_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  exact ⟨decrypt_message_ok root hargs hfmt hc self sender salt iv ct tag rpk key ks hpk ha
    hd p hdec, hlen _ _ _ _ _ hdec⟩

/-- conditional: if `decrypt_message` returns `Ok p`, then `p` is as long as `ct`, whichever attempt
returned the plaintext. The hypothesis is the returned value; the outcomes of `public_key`,
`agree_key` and the two decryptions are not assumed. Hypotheses: the `context` law `CryptoCtxLaw`
at line 131, the length law `AesGcmDecryptSpec`, and the returned value. -/
theorem decrypt_message_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hc131 : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hlen : AesGcmDecryptSpec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (p : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Ok p)) :
    ∃ s, zvecDeref p = ok s ∧ s.length = ct.length := by
  unfold ec_crypto.ECDHPrivateKey.decrypt_message at h
  obtain ⟨r, -, h⟩ := dec_bind_ok h
  rcases r with val | e
  swap
  · simp [CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from] at h
  obtain ⟨cf, hcf, h⟩ := dec_bind_ok h
  simp [CoreOpsTry.branch] at hcf
  subst hcf
  dsimp only at h
  obtain ⟨r1, -, h⟩ := dec_bind_ok h
  obtain ⟨a, -, h⟩ := dec_bind_ok h
  obtain ⟨s1, -, h⟩ := dec_bind_ok h
  obtain ⟨s2, -, h⟩ := dec_bind_ok h
  obtain ⟨r2, -, h⟩ := dec_bind_ok h
  rcases r2 with val1 | e
  swap
  · simp [CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from] at h
  obtain ⟨cf, hcf, h⟩ := dec_bind_ok h
  simp [CoreOpsTry.branch] at hcf
  subst hcf
  dsimp only at h
  obtain ⟨s3, -, h⟩ := dec_bind_ok h
  obtain ⟨r3, hr3, h⟩ := dec_bind_ok h
  rcases r3 with p' | e1
  · simp [Result.or_else] at h
    subst h
    exact hlen _ _ _ _ _ hr3
  simp [Result.or_else, closureCallOnce] at h
  obtain ⟨r, -, h⟩ := dec_bind_ok h
  obtain ⟨a, -, h⟩ := dec_bind_ok h
  obtain ⟨s6, -, h⟩ := dec_bind_ok h
  obtain ⟨s7, -, h⟩ := dec_bind_ok h
  obtain ⟨r1, -, h⟩ := dec_bind_ok h
  rcases r1 with k2 | e
  swap
  · simp [CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual,
      FromSame.from] at h
  obtain ⟨cf, hcf, h⟩ := dec_bind_ok h
  simp [CoreOpsTry.branch] at hcf
  subst hcf
  dsimp only at h
  obtain ⟨s8, -, h⟩ := dec_bind_ok h
  obtain ⟨r2, hr2, h⟩ := dec_bind_ok h
  obtain ⟨a1, -, h⟩ := dec_bind_ok h
  obtain ⟨s9, -, h⟩ := dec_bind_ok h
  obtain ⟨s10, -, h⟩ := dec_bind_ok h
  rw [dec_ctx_ok_of hc131 _ _ _ h] at hr2
  exact hlen _ _ _ _ _ hr2

/-- conditional: if `public_key` and `agree_key` (version `Current`) return `Ok`, the first
`aes_gcm_decrypt` returns `Err e1`, whatever `e1` is, `agree_key` with the version `LegacyTruncated`
returns `Ok`, and the second `aes_gcm_decrypt` returns `Ok p`, then `decrypt_message` returns `Ok
p`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` laws `AnyCtxLaw`
at lines 117 and 129 and `CryptoCtxLaw` at line 131, and the outcomes of the calls. Model limit: the
two `agree_key` calls run the same `hkdf_extract` and point-conversion steps before the version is
used. A run in which one of these shared steps gives different outcomes in the two calls is outside
the model. -/
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨a2, h2⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:129: agree_key failed")
  obtain ⟨s2, f2⟩ := hfmt a2
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:131: aes_gcm_decrypt failed")
  obtain ⟨s3, f3⟩ := hfmt a3
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec1, ha2, hd2, hdec2, h1, f1, h2, f2, h3, f3, hc.1, hc131.1,
    closureCallOnce,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if `public_key` returns `Err e`, then `decrypt_message` returns the same error `e`
(the error value is passed through unchanged). In the Rust source the `?` returns at this point,
before `agree_key` is called. Hypothesis: the outcome of the call. No law is needed. -/
theorem decrypt_message_err_public_key
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (e : anyhow.Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Err e)) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok (.Err e) := by
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if `public_key` returns `Ok` and `agree_key` (version `Current`) returns `Err e`,
then `decrypt_message` returns an error with the same root cause as `e`. The statement assumes only
that `agree_key` returned `Err e`. In the Rust source `agree_key` returns an error when `sender`
does not decode, and the `?` of line 117 returns at this point, before `aes_gcm_decrypt` is called.
Hypotheses: the shared laws for `from_str_nonconst` and `format`, the
`context` law `AnyCtxLaw` at line 117, and the outcomes of the calls. -/
theorem decrypt_message_err_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (e : anyhow.Error)
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = ok
    (.Err e') ∧ root e' = root e := by
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨e', he, hr⟩ := hc.2 e s1
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, h1, f1, he,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1`, and the legacy `agree_key` returns
`Err e`, then `decrypt_message` returns an error with the same root cause as `e`. The first error
`e1` does not matter. In the Rust source the `?` of line 129 returns at this point, before the
second `aes_gcm_decrypt` is called. Hypotheses: the shared laws for `from_str_nonconst` and
`format`, the `context` law `AnyCtxLaw` at lines 117 and 129, and the outcomes of the calls. The
statement covers an error of the legacy `agree_key` at a step that depends on the version. Model
limit: the two `agree_key` calls run the same `hkdf_extract` and point-conversion steps before the
version is used. A run in which one of these shared steps gives different outcomes in the two calls
is outside the model. -/
theorem decrypt_message_err_legacy_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨a2, h2⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:129: agree_key failed")
  obtain ⟨s2, f2⟩ := hfmt a2
  obtain ⟨e', he, hr⟩ := hc.2 e s2
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec1, ha2, h1, f1, h2, f2, he, hc.1,
    closureCallOnce,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1` and the second one, with the legacy
key, returns `Err e`, then `decrypt_message` returns an error whose root cause is the crypto error
`e` of the second call. The first error `e1` is dropped, whatever it is. Hypotheses: the shared laws
for `from_str_nonconst` and `format`, the `context` laws `AnyCtxLaw` at lines 117 and 129 and
`CryptoCtxLaw` at line 131, and the outcomes of the calls. Model limit: the two `agree_key` calls
run the same `hkdf_extract` and point-conversion steps before the version is used. A run in which
one of these shared steps gives different outcomes in the two calls is outside the model. -/
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨a2, h2⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:129: agree_key failed")
  obtain ⟨s2, f2⟩ := hfmt a2
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:131: aes_gcm_decrypt failed")
  obtain ⟨s3, f3⟩ := hfmt a3
  obtain ⟨e', he, hr⟩ := hc131.2 e s3
  refine ⟨e', ?_, hr⟩
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec1, ha2, hd2, hdec2, h1, f1, h2, f2, h3, f3, he, hc.1,
    closureCallOnce,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if `public_key` fails, then `decrypt_message` returns the same `fail x`.
Hypothesis: the outcome of the call. No law is needed. -/
theorem decrypt_message_fail_public_key (self : ec_crypto.ECDHPrivateKey)
    (sender salt iv ct tag : Slice Std.U8)
    (x : Error) (hpk : ec_crypto.ECDHPrivateKey.public_key self = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if `public_key` returns `Ok` and `agree_key` (version `Current`) fails, then
`decrypt_message` returns the same `fail x`. Hypotheses: the outcomes of the two calls. No law is
needed. -/
theorem decrypt_message_fail_agree_key (self : ec_crypto.ECDHPrivateKey)
    (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8) (x : Error)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- conditional: if the first `aes_gcm_decrypt` returns `Err e1` and the legacy `agree_key` fails,
then `decrypt_message` returns the same `fail x`. Hypotheses: the shared laws for
`from_str_nonconst` and `format`, the `context` law `AnyCtxLaw` at lines 117 and 129, and the
outcomes of the calls. Model limit: the two `agree_key` calls run the same `hkdf_extract` and
point-conversion steps before the version is used. A run in which one of these shared steps gives
different outcomes in the two calls is outside the model. -/
theorem decrypt_message_fail_legacy_agree_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨a2, h2⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:129: agree_key failed")
  obtain ⟨s2, f2⟩ := hfmt a2
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec1, ha2, h1, f1, h2, f2, hc.1,
    closureCallOnce,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

/-- exact: the fallback closure of `decrypt_message` does not look at the error of the first
decryption. Its result is the same for every error value. -/
theorem decrypt_message_closure_ignores_error
    (c : closure)
    (e1 e2 : keystore2_crypto.error.Error) :
    closureCallOnce c e1 = closureCallOnce c e2 := by
  rfl

/-- conditional: if `deref` of the derived key fails, then `decrypt_message` returns the same
`fail x`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` law
`AnyCtxLaw` at line 117 (the call before it passes through `context`), and the outcomes of the
earlier calls and of this one. -/
theorem decrypt_message_fail_deref_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (sender salt iv ct tag : Slice Std.U8)
    (rpk : alloc.vec.Vec Std.U8)
    (key : keystore2_crypto.zvec.ZVec)
    (hpk : ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok rpk))
    (ha : ec_crypto.ECDHPrivateKey.agree_key self salt sender sender
      (Vec.deref rpk) keystore2_crypto.EcdhComputeKeyVersion.Current = ok (.Ok key))
    (x : Error)
    (hd : zvecDeref key = fail x) :
    ec_crypto.ECDHPrivateKey.decrypt_message self sender salt iv ct tag = fail x := by
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, h1, f1, hc.1,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]
/-- conditional: if the first `aes_gcm_decrypt` fails, then `decrypt_message` returns the same
`fail x`. In the Rust source a panic is not an `Err`, so it does not reach the closure of `or_else`.
Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` law `AnyCtxLaw` at
line 117, and the outcomes of the earlier calls and of this one. -/
theorem decrypt_message_fail_first_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec, h1, f1, hc.1,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]
/-- conditional: if `deref` of the legacy key fails, then `decrypt_message` returns the same
`fail x`. Hypotheses: the shared laws for `from_str_nonconst` and `format`, the `context` law
`AnyCtxLaw` at lines 117 and 129, and the outcomes of the earlier calls and of this one. Model
limit: the two `agree_key` calls run the same `hkdf_extract` and point-conversion steps before the
version is used. A run in which one of these shared steps gives different outcomes in the two calls
is outside the model. -/
theorem decrypt_message_fail_deref_legacy_key (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨a2, h2⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:129: agree_key failed")
  obtain ⟨s2, f2⟩ := hfmt a2
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec1, ha2, hd2, h1, f1, h2, f2, hc.1,
    closureCallOnce,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]
/-- conditional: if the second `aes_gcm_decrypt`, with the legacy key, fails, then
`decrypt_message` returns the same `fail x`. Hypotheses: the shared laws for `from_str_nonconst` and
`format`, the `context` law `AnyCtxLaw` at lines 117 and 129, and the outcomes of the earlier calls
and of this one. Model limit: the two `agree_key` calls run the same `hkdf_extract` and
point-conversion steps before the version is used. A run in which one of these shared steps gives
different outcomes in the two calls is outside the model. -/
theorem decrypt_message_fail_legacy_decrypt (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hc : AnyCtxLaw root keystore2_crypto.zvec.ZVec)
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
  obtain ⟨a1, h1⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:117: agree_key failed")
  obtain ⟨s1, f1⟩ := hfmt a1
  obtain ⟨a2, h2⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:129: agree_key failed")
  obtain ⟨s2, f2⟩ := hfmt a2
  obtain ⟨a3, h3⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:131: aes_gcm_decrypt failed")
  obtain ⟨s3, f3⟩ := hfmt a3
  unfold ec_crypto.ECDHPrivateKey.decrypt_message
  simp [hpk, ha, hd, hdec1, ha2, hd2, hdec2, h1, f1, h2, f2, h3, f3, hc.1,
    closureCallOnce,
    core.hint.must_use, CoreOpsTry.branch,
    CoreOpsTry_traitFromResidualResult.from_residual,
    FromSame.from,
    Result.or_else]

end Keystore2Verify.EcCrypto
