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
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:37: parsing failed")
  obtain ⟨s, hs⟩ := hfmt a
  unfold ec_crypto.ECDHPrivateKey.from_private_key
  open core.result.Result P.Insts.CoreOpsFunctionFnOnceTupleECKeyECDHPrivateKey in
  simp [hparse, ha, hs, map, core.hint.must_use, ec_crypto.ECDHPrivateKey.constructor,
    call_once]
  exact hctx.1 _ _

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
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:37: parsing failed")
  obtain ⟨s, hs⟩ := hfmt a
  obtain ⟨e', h1, h2⟩ := hctx.2 e s
  refine ⟨e', ?_, h2⟩
  unfold ec_crypto.ECDHPrivateKey.from_private_key
  open core.result.Result P.Insts.CoreOpsFunctionFnOnceTupleECKeyECDHPrivateKey in
  simp [hparse, ha, hs, map, core.hint.must_use, ec_crypto.ECDHPrivateKey.constructor,
    call_once]
  exact h1

/-- conditional: if `ec_key_parse_private_key buf` fails, then `from_private_key buf` returns the
same `fail x`. Hypothesis: the outcome of the call. No law is needed. -/
theorem from_private_key_fail (buf : Slice Std.U8) (x : Error)
    (hparse : keystore2_crypto.ec_key_parse_private_key buf = fail x) :
    ec_crypto.ECDHPrivateKey.from_private_key buf = fail x := by
  unfold ec_crypto.ECDHPrivateKey.from_private_key
  simp [hparse]

end Keystore2Verify.EcCrypto
