import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- conditional: if `ec_key_get0_public_key` gives the point `pt`, `get_point` gives `eps` and
`ec_point_point_to_oct eps` returns `Ok v`, then `public_key` returns `Ok v`. Hypotheses: the shared
laws for `from_str_nonconst`, `format` and the `context` of a crypto error (`CryptoCtxLaw`), and the
three outcomes. -/
theorem public_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (self : ec_crypto.ECDHPrivateKey) (pt : keystore2_crypto.BorrowedECPoint)
    (eps : keystore2_crypto_bindgen.ec_point_st) (v : alloc.vec.Vec Std.U8)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = ok (.Ok v)) :
    ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok v) := by
  sorry

/-- conditional: under the hypotheses of `public_key_ok` and the length law `EcPointPointToOctSpec`,
`public_key` returns `Ok v` and `v` has between 1 and 133 bytes. -/
theorem public_key_ok_length (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8)) (hlen : EcPointPointToOctSpec)
    (self : ec_crypto.ECDHPrivateKey) (pt : keystore2_crypto.BorrowedECPoint)
    (eps : keystore2_crypto_bindgen.ec_point_st) (v : alloc.vec.Vec Std.U8)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = ok (.Ok v)) :
    ec_crypto.ECDHPrivateKey.public_key self = ok (.Ok v) ∧
      1 ≤ v.val.length ∧ v.val.length ≤ 133 := by
  sorry

/-- conditional: if `ec_key_get0_public_key` gives the point `pt`, `get_point` gives `eps` and
`ec_point_point_to_oct eps` returns `Err e`, then `public_key` returns an error whose root cause is
the crypto error `e`. Hypotheses: the same laws as `public_key_ok`, and the three outcomes. -/
theorem public_key_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root (alloc.vec.Vec Std.U8))
    (self : ec_crypto.ECDHPrivateKey) (pt : keystore2_crypto.BorrowedECPoint)
    (eps : keystore2_crypto_bindgen.ec_point_st) (e : keystore2_crypto.error.Error)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = ok eps)
    (hoct : keystore2_crypto.ec_point_point_to_oct eps = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.public_key self = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if `get_point` panics on the point of the key (in Rust: the pointer is null), then
`public_key` panics in the same way, and nothing else is called. Hypotheses: the outcomes of
`ec_key_get0_public_key` and `get_point`. No law is needed. -/
theorem public_key_fail_get_point (self : ec_crypto.ECDHPrivateKey)
    (pt : keystore2_crypto.BorrowedECPoint) (x : Error)
    (hkey : keystore2_crypto.ec_key_get0_public_key self = ok pt)
    (hpt : keystore2_crypto.BorrowedECPoint.get_point pt = fail x) :
    ec_crypto.ECDHPrivateKey.public_key self = fail x := by
  sorry

end Keystore2Verify.EcCrypto
