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
  sorry

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
  sorry

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
  sorry

/-- conditional: if `ec_key_marshal_private_key key` fails, then `private_key key` returns the same
`fail x`. Hypothesis: the outcome of the call. No law is needed. -/
theorem private_key_fail (self : ec_crypto.ECDHPrivateKey) (x : Error)
    (hm : keystore2_crypto.ec_key_marshal_private_key self = fail x) :
    ec_crypto.ECDHPrivateKey.private_key self = fail x := by
  sorry


/-- Length of the private key bytes returned to the caller. -/
theorem private_key_ok_length_of_result (root : anyhow.Error → ErrRoot)
    (hctx : CryptoCtxLaw root keystore2_crypto.zvec.ZVec) (hlen : EcKeyMarshalPrivateKeySpec)
    (self : ec_crypto.ECDHPrivateKey) (z : keystore2_crypto.zvec.ZVec)
    (h : ec_crypto.ECDHPrivateKey.private_key self = ok (.Ok z)) :
    ∃ s, zvecDeref z = ok s ∧ s.length = 73 := by
  sorry

end Keystore2Verify.EcCrypto
