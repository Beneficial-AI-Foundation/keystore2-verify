import Keystore2Verify.Specs.Defs.Permission

/-!
# Definitions for the statements about `attestation_key_utils.rs`

The `context` call on a keystore2 error with a `String` message, for any success type. The
statements about other files that add a context to a keystore2 error use it too. Nothing here is
an axiom.
-/

namespace Keystore2Verify.AttestationKeyUtils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.result.Result.Insts.AnyhowContext
open anyhow.context.ext.StdError
open error.Error.Insts
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay

/-- The `context` assumption at the call `result.context(s)` where `result` holds a keystore2
error and a value of type `T`, and the message `s` is a `String`. The root cause of the new
error is that keystore2 error. 
Record `ks2-ext-core-result-result-insts-anyhowcontext-context`. -/
abbrev KsCtxAssumption (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun x => ErrRoot.ks x) root
    (context (T := T) (Blanket CoreErrorError) StringDisplay)

/-- The type of a loaded attestation key: its guard, key blob, certificate and blob metadata. -/
abbrev Loaded : Type :=
  database.KeyIdGuard × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8 × database.BlobMetaData

end Keystore2Verify.AttestationKeyUtils
