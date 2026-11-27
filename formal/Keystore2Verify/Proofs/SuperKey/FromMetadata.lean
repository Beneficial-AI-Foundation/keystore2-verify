import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

/-! The map of a `BlobMetaData` binds the tag 0 to the `EncryptedBy` entry and the tag 6 to the
`MaxBootLevel` entry. In the three statements, `ents` reads the entries of the map. -/

/-- conditional: if the metadata has an `EncryptedBy` entry `KeyId(k)`, the function returns
`Some(DatabaseId(k))`, whatever else the metadata holds. In the Rust source this path returns
before `max_boot_level` is called. Hypothesis: the assumption for `HashMap::get` on the map. -/
theorem SuperKeyIdentifier_from_metadata_key_id (ents : MetaEntries) (hget : MetaGetSpec ents)
    (metadata : database.BlobMetaData) (k : Std.I64)
    (h : (0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId k)) ∈
      ents metadata.data) :
    super_key.SuperKeyIdentifier.from_metadata metadata =
      ok (some (super_key.SuperKeyIdentifier.DatabaseId k)) := by
  sorry

/-- conditional: if the metadata has no `EncryptedBy` entry `KeyId(_)` (there is no `EncryptedBy`
entry, or it is `Password`) and it has a `MaxBootLevel` entry `n`, the function returns
`Some(BootLevel(n as usize))`. The cast `i32 as usize` keeps a number from `0` to `i32::MAX`, and
gives `n + 2^64` for a negative `n` on a 64-bit target (the statement uses the cast of the
translation, which follows the width of `usize`). Hypothesis: the assumption for `HashMap::get` on
the map. -/
theorem SuperKeyIdentifier_from_metadata_boot_level (ents : MetaEntries)
    (hget : MetaGetSpec ents) (metadata : database.BlobMetaData) (n : Std.I32)
    (hno : ∀ k, (0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId k)) ∉
      ents metadata.data)
    (h : (6#i64, database.BlobMetaEntry.MaxBootLevel n) ∈ ents metadata.data) :
    super_key.SuperKeyIdentifier.from_metadata metadata =
      ok (some (super_key.SuperKeyIdentifier.BootLevel (IScalar.hcast .Usize n))) := by
  sorry

/-- conditional: if the metadata has no `EncryptedBy` entry `KeyId(_)` and no `MaxBootLevel`
entry, the function returns `None`. Hypothesis: the assumption for `HashMap::get` on the map. -/
theorem SuperKeyIdentifier_from_metadata_none (ents : MetaEntries) (hget : MetaGetSpec ents)
    (metadata : database.BlobMetaData)
    (hno : ∀ k, (0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId k)) ∉
      ents metadata.data)
    (hnb : ∀ n, (6#i64, database.BlobMetaEntry.MaxBootLevel n) ∉ ents metadata.data) :
    super_key.SuperKeyIdentifier.from_metadata metadata = ok none := by
  sorry

end Keystore2Verify.SuperKey
