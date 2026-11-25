import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `boot_level_keys`

The cache of boot level keys keeps its keys in a `VecDeque`, which the translation leaves opaque.
The statements below look at it through the `List` view of the shared laws in `Externals`.
-/

namespace Keystore2Verify.BootLevelKeys
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals

/-- The `List` view of a cache queue, front first (the shared observation of `VecDeque`). -/
abbrev View := ZVecQueue → List keystore2_crypto.zvec.ZVec

/-- The bytes `b` spell the ASCII text `text`. -/
def BytesAre (b : List Std.U8) (text : String) : Prop :=
  b.map (fun x => x.val) = text.toList.map Char.toNat

/-- The shared law `ResultContextLaw` for the call `Result::context` that the cache uses on the
result of `get_hkdf_key` and of `expand_key`: an `Ok (Option ZVec)` of `anyhow::Error` stays `Ok`,
and an `Err` keeps its root cause. The message type is `String`. -/
def ContextKeyLaw (root : anyhow.Error → ErrRoot) : Prop :=
  AnyCtxLaw root (Option keystore2_crypto.zvec.ZVec)

/-- The shared law `ResultContextLaw` for the call `Result::context` that `expand_key` uses on the
result of `hkdf_expand`: an `Ok` stays `Ok`, and an `Err x` of `keystore2_crypto::error::Error`
becomes an error whose root cause is `x`. The message type is `String`. -/
def ContextCryptoLaw (root : anyhow.Error → ErrRoot) : Prop :=
  CryptoCtxLaw root (Option keystore2_crypto.zvec.ZVec)

end Keystore2Verify.BootLevelKeys
