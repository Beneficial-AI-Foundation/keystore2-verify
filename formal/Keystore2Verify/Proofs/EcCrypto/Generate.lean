import Keystore2Verify.Specs.Defs.EcCrypto

namespace Keystore2Verify.EcCrypto
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- conditional: if `ec_key_generate_key` returns `Ok k`, then `generate` returns `Ok k` (the key is
passed on unchanged). Hypotheses: the shared laws for `from_str_nonconst`, `format` and the
`context` of a crypto error (`CryptoCtxLaw`), and the outcome of the call. -/
theorem generate_ok (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (k : keystore2_crypto.ECKey)
    (hgen : keystore2_crypto.ec_key_generate_key = ok (.Ok k)) :
    ec_crypto.ECDHPrivateKey.generate = ok (.Ok k) := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:32: generation failed")
  obtain ⟨s, hs⟩ := hfmt a
  unfold ec_crypto.ECDHPrivateKey.generate
  open core.result.Result P.Insts.CoreOpsFunctionFnOnceTupleECKeyECDHPrivateKey in
  simp [hgen, ha, hs, map, core.hint.must_use, ec_crypto.ECDHPrivateKey.constructor,
    call_once]
  exact hctx.1 _ _

/-- conditional: if `ec_key_generate_key` returns `Err e`, then `generate` returns an error whose
root cause is the crypto error `e`. Hypotheses: the same laws as `generate_ok`, and the outcome of
the call. -/
theorem generate_err (root : anyhow.Error → ErrRoot)
    (hargs : CoreFmtArgumentsFromStrNonconstSpec) (hfmt : AllocFmtFormatSpec)
    (hctx : CryptoCtxLaw root ec_crypto.ECDHPrivateKey)
    (e : keystore2_crypto.error.Error)
    (hgen : keystore2_crypto.ec_key_generate_key = ok (.Err e)) :
    ∃ e', ec_crypto.ECDHPrivateKey.generate = ok (.Err e') ∧ root e' = ErrRoot.crypto e := by
  obtain ⟨a, ha⟩ := hargs (toStr "keystore2/src/ec_crypto.rs:32: generation failed")
  obtain ⟨s, hs⟩ := hfmt a
  obtain ⟨e', h1, h2⟩ := hctx.2 e s
  refine ⟨e', ?_, h2⟩
  unfold ec_crypto.ECDHPrivateKey.generate
  open core.result.Result P.Insts.CoreOpsFunctionFnOnceTupleECKeyECDHPrivateKey in
  simp [hgen, ha, hs, map, core.hint.must_use, ec_crypto.ECDHPrivateKey.constructor,
    call_once]
  exact h1

/-- conditional: if `ec_key_generate_key` fails, then `generate` returns the same `fail x`.
Hypothesis: the outcome of the call. No law is needed. -/
theorem generate_fail (x : Error)
    (hgen : keystore2_crypto.ec_key_generate_key = fail x) :
    ec_crypto.ECDHPrivateKey.generate = fail x := by
  unfold ec_crypto.ECDHPrivateKey.generate
  simp [hgen]

end Keystore2Verify.EcCrypto
