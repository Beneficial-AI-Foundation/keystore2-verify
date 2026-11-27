import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

/-- conditional: for `DatabaseId(id)`, the function returns the metadata with the entry at the tag 0
(`EncryptedBy`) set to `EncryptedBy(KeyId(id))`; every other entry is unchanged, and an
`EncryptedBy` entry that was there is replaced. Hypothesis: the assumption for `HashMap::insert` on
the map, read through `ents`. -/
theorem SuperKeyIdentifier_add_to_metadata_database_id (ents : MetaEntries)
    (hins : MetaInsertSpec ents) (id : Std.I64) (metadata : database.BlobMetaData) :
    ∃ m, super_key.SuperKeyIdentifier.add_to_metadata
        (super_key.SuperKeyIdentifier.DatabaseId id) metadata = ok m ∧
      MetaEntriesAre ents metadata m
        [(0#i64, database.BlobMetaEntry.EncryptedBy (database.EncryptedBy.KeyId id))] := by
  sorry

/-- conditional: for `BootLevel(level)`, the function returns the metadata with the entry at the tag
6 (`MaxBootLevel`) set to `MaxBootLevel(level as i32)`; every other entry is unchanged, and an
`EncryptedBy` entry that was there is not removed. The cast `usize as i32` keeps the low 32 bits: a
level above `i32::MAX` is stored as its low 32 bits, and the limit `MAX_MAX_BOOT_LEVEL` is not
checked here. Hypothesis: the assumption for `HashMap::insert` on the map, read through `ents`. -/
theorem SuperKeyIdentifier_add_to_metadata_boot_level (ents : MetaEntries)
    (hins : MetaInsertSpec ents) (level : boot_level_keys.BootLevel)
    (metadata : database.BlobMetaData) :
    ∃ m, super_key.SuperKeyIdentifier.add_to_metadata
        (super_key.SuperKeyIdentifier.BootLevel level) metadata = ok m ∧
      MetaEntriesAre ents metadata m
        [(6#i64, database.BlobMetaEntry.MaxBootLevel (UScalar.hcast .I32 level))] := by
  sorry

end Keystore2Verify.SuperKey
