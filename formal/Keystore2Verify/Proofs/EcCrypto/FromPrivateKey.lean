import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- conditional: if `ec_key_parse_private_key buf` returns `Ok k`, then `from_private_key buf`
returns `Ok k`. The whole slice `buf` goes to the parser, and `from_private_key` checks nothing
about it (not its length either). Hypotheses: the shared laws for `from_str_nonconst`, `format` and
`CryptoCtxLaw`, and the outcome of the call. -/
theorem from_private_key_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (buf : Slice Std.U8) (k : keystore2_crypto.ECKey)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = ok (.Ok k)) :
    ec_crypto.ECDHPrivateKey.from_private_key buf = ok (.Ok k) := by
  sorry

/-- conditional: if `ec_key_parse_private_key buf` returns `Err e`, then `from_private_key buf`
returns an error whose root cause is the crypto error `e`. Hypotheses: the same laws as
`from_private_key_ok`, and the outcome of the call. -/
theorem from_private_key_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (buf : Slice Std.U8) (e : keystore2_crypto.error.Error)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.from_private_key buf = ok (.Err e') ∧
      root e' = ErrRoot.crypto e := by
  sorry

/-- conditional: if `ec_key_parse_private_key buf` fails, then `from_private_key buf` returns the
same `fail x`. Hypothesis: the outcome of the call. No law is needed. -/
theorem from_private_key_fail (buf : Slice Std.U8) (x : Error)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = fail x) :
    ec_crypto.ECDHPrivateKey.from_private_key buf = fail x := by
  sorry

end Keystore2Verify.EcCrypto
