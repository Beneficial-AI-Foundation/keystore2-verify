import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- conditional: if `ec_key_marshal_private_key key` returns `Ok z`, then `private_key key` returns
`Ok z`. Hypotheses: the shared laws for `from_str_nonconst`, `format` and the `context` of a crypto
error (`CryptoCtxLaw`), and the outcome of the call. -/
theorem private_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = ok (.Ok z)) :
    ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z) := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:42: marshalling failed")
  obtain ⟨s, hs⟩ := hfmt a
  unfold ec_crypto.ECDHPrivateKey.private_key
  simp [hm, ha, hs, core.hint.must_use]
  exact hctx.1 _ _

/-- conditional: if `ec_key_marshal_private_key key` returns `Ok z`, then `private_key key` returns
`Ok z` and `z` has 73 bytes. Hypotheses: the laws of `private_key_ok`, the length law
`EcKeyMarshalPrivateKeySpec`, and the outcome of the call. -/
theorem private_key_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (hlen : EcKeyMarshalPrivateKeySpec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = ok (.Ok z)) :
    ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z) ∧
      ∃ s, zvecDeref z = ok s ∧ s.length = 73 := by
  exact ⟨private_key_ok root hargs hfmt hctx self z hm, hlen self z hm⟩

/-- conditional: if `ec_key_marshal_private_key key` returns `Err e`, then `private_key key` returns
an error whose root cause is the crypto error `e`. Hypotheses: the same laws as `private_key_ok`,
and the outcome of the call. -/
theorem private_key_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec)
    (self : ec_crypto.ECDHPrivateKey) (e : keystore2_crypto.error.Error)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.private_key self = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:42: marshalling failed")
  obtain ⟨s, hs⟩ := hfmt a
  obtain ⟨e', h1, h2⟩ := hctx.2 e s
  refine ⟨e', ?_, h2⟩
  unfold ec_crypto.ECDHPrivateKey.private_key
  simp [hm, ha, hs, core.hint.must_use]
  exact h1

/-- conditional: if `ec_key_marshal_private_key key` fails, then `private_key key` returns the same
`fail x`. Hypothesis: the outcome of the call. No law is needed. -/
theorem private_key_fail (self : ec_crypto.ECDHPrivateKey) (x : Error)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = fail x) :
    ec_crypto.ECDHPrivateKey.private_key self = fail x := by
  unfold ec_crypto.ECDHPrivateKey.private_key
  simp [hm]


/-- Length of the private key bytes returned to the caller. -/
theorem private_key_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec) (hlen : EcKeyMarshalPrivateKeySpec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z)) :
    ∃ s, zvecDeref z = ok s ∧ s.length = 73 := by
  unfold ec_crypto.ECDHPrivateKey.private_key at h
  cases hm : keystore2_crypto.ec_key_marshal_private_key self with
  | ret r =>
    open core.fmt.Arguments in
    cases hA : from_str_nonconst (toStr
        "keystore2/src/ec_crypto.rs:42: marshalling failed") with
    | ret a =>
      cases hF : alloc.fmt.format a with
      | ret s =>
        cases r with
        | Ok z' =>
          simp [hm, hA, hF, core.hint.must_use, hctx.1] at h
          subst h
          exact hlen self _ hm
        | Err e =>
          obtain ⟨e', h1, _⟩ := hctx.2 e s
          simp [hm, hA, hF, core.hint.must_use, h1] at h
      | vis i k => simp [hm, hA, hF] at h
      | div => simp [hm, hA, hF] at h
    | vis i k => simp [hm, hA] at h
    | div => simp [hm, hA] at h
  | vis i k => simp [hm] at h
  | div => simp [hm] at h

end Keystore2Verify.EcCrypto
