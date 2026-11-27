import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `entropy.rs`

The `context` call of `get_entropy` is the shared assumption `ResultContextLaw` at one
instance. Nothing here is an axiom.
-/

namespace Keystore2Verify.Entropy
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.result.Result.Insts.AnyhowContext
open anyhow.context.ext.StdError
open keystore2_crypto.error.Error.Insts

/-- The `context` assumption at the call `result.context("..")` where `result` holds a crypto
error and a value of type `T`, and the message is a `&str` constant. The root cause of the new
error is that crypto error. 
Record `ks2-ext-core-result-result-insts-anyhowcontext-context`. -/
abbrev CryptoStrCtxAssumption (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun x => ErrRoot.crypto x) root
    (context (T := T) (Blanket CoreErrorError)
      (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay))

end Keystore2Verify.Entropy
