import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `boot_level_keys`

The cache of boot level keys keeps its keys in a `VecDeque`, which the translation leaves opaque.
The statements below look at it through the `List` view of the shared laws in `Externals`.
-/

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open keystore2.core.result.Result.Insts.AnyhowContext renaming context → resultContext
open keystore2.anyhow.context.ext.StdError renaming Blanket → stdBlanket
open keystore2.keystore2_crypto.error.Error.Insts renaming CoreErrorError → cryptoErrorError
open keystore2.alloc.collections
open keystore2.anyhow.Error.Insts renaming AnyhowContextExtStdError → anyhowExtStdError
open keystore2.alloc.string.String.Insts renaming CoreFmtDisplay → stringDisplay

/-- The queue type of the cache: a `VecDeque` of secret vectors with the global allocator. -/
abbrev Queue :=
  vec_deque.VecDeque keystore2_crypto.zvec.ZVec alloc.alloc.Global

/-- The `List` view of a cache queue, front first (the shared observation of `VecDeque`). -/
abbrev View := Queue → List keystore2_crypto.zvec.ZVec

/-- The bytes `b` spell the ASCII text `text`. -/
def BytesAre (b : List Std.U8) (text : String) : Prop :=
  b.map (fun x => x.val) = text.toList.map Char.toNat

/-- The shared law `ResultContextLaw` for the call `Result::context` that the cache uses on the
result of `get_hkdf_key` and of `expand_key`: an `Ok (Option ZVec)` of `anyhow::Error` stays `Ok`,
and an `Err` keeps its root cause. The message type is `String`. -/
def ContextKeyLaw (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw root root
    (resultContext (T := Option keystore2_crypto.zvec.ZVec)
      anyhowExtStdError stringDisplay)

/-- The shared law `ResultContextLaw` for the call `Result::context` that `expand_key` uses on the
result of `hkdf_expand`: an `Ok` stays `Ok`, and an `Err x` of `keystore2_crypto::error::Error`
becomes an error whose root cause is `x`. The message type is `String`. -/
def ContextCryptoLaw (root : anyhow.Error → ErrRoot) : Prop :=
  ResultContextLaw ErrRoot.crypto root
    (resultContext (T := Option keystore2_crypto.zvec.ZVec)
      (stdBlanket cryptoErrorError)
      stringDisplay)

end Keystore2Verify.BootLevelKeys
