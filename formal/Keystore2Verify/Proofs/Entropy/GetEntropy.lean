import Keystore2Verify.Specs.Defs.Entropy

namespace Keystore2Verify.Entropy
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2_crypto.error.Error.Insts

/-- conditional: if `generate_random_data size` returns `Ok v`, `get_entropy size` returns
`Ok v`: the bytes pass unchanged and `size` is passed unchanged to the generator.
Hypotheses: the outcome of `generate_random_data` (random data), and the assumption about
`context` for a
crypto error with a `&str` message (`CryptoStrCtxAssumption`). -/
theorem get_entropy_ok (root : anyhow.Error → ErrRoot)
    (hctx : CryptoStrCtxAssumption root (alloc.vec.Vec Std.U8))
    (size : Std.Usize) (v : alloc.vec.Vec Std.U8)
    (h : keystore2_crypto.generate_random_data size = ok (.Ok v)) :
    entropy.get_entropy size = ok (.Ok v) := by
  sorry

/-- conditional: if `generate_random_data size` returns the crypto error `ce`, `get_entropy size`
returns an error whose root cause is `ce`. Hypotheses: the outcome of `generate_random_data`, and
`CryptoStrCtxAssumption`. -/
theorem get_entropy_err (root : anyhow.Error → ErrRoot)
    (hctx : CryptoStrCtxAssumption root (alloc.vec.Vec Std.U8))
    (size : Std.Usize) (ce : keystore2_crypto.error.Error)
    (h : keystore2_crypto.generate_random_data size = ok (.Err ce)) :
    ∃ e, entropy.get_entropy size = ok (.Err e) ∧ root e = ErrRoot.crypto ce := by
  sorry
