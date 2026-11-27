import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.BlobMetaEntry renaming db_tag → blobMetaEntryDbTag
open database.BlobMetaData renaming add → blobMetaDataAdd
open database.BlobMetaData.Insts
open database.BlobMetaEntry.Insts
open CoreDefaultDefault renaming default → blobMetaDataDefault
open CoreCmpPartialEqBlobMetaData renaming eq → blobMetaDataEq
open database.BlobMetaData renaming encrypted_by → bmdEncryptedBy
open database.BlobMetaData renaming salt → bmdSalt
open database.BlobMetaData renaming iv → bmdIv
open database.BlobMetaData renaming aead_tag → bmdAeadTag
open database.BlobMetaData renaming km_uuid → bmdKmUuid
open database.BlobMetaData renaming public_key → bmdPublicKey
open database.BlobMetaData renaming max_boot_level → bmdMaxBootLevel

/-- conditional: `add` never fails. The new map holds the entry under its number (the result of
`db_tag`), and every other number keeps its entry. An earlier entry of the same variant is
replaced. Hypothesis: `HashMapInsertSpec` (assumption about `HashMap::insert`) for the view
`view`. -/
theorem blob_meta_data_add (view : MetaView database.BlobMetaEntry)
    (hins : HashMapInsertSpec view) (self : database.BlobMetaData)
    (e : database.BlobMetaEntry) :
    ∃ t md, blobMetaEntryDbTag e = ok t ∧ blobMetaDataAdd self e = ok md ∧
      view md.data t = some e ∧ ∀ j, j ≠ t → view md.data j = view self.data j := by
  sorry

/-- conditional: `default` never fails and returns an empty map. Hypothesis: `HashMapDefaultSpec`
for the view `view`. -/
theorem blob_meta_data_default (view : MetaView database.BlobMetaEntry)
    (hdef : HashMapDefaultSpec database.BlobMetaEntry view) :
    ∃ md, blobMetaDataDefault = ok md ∧ ∀ k, view md.data k = none := by
  sorry

/-- conditional: `eq` never fails. It returns `true` exactly when both maps have the same numbers,
with equal entries under each. Hypothesis: `HashMapEqSpec` for the view `view` and the derived
`eq` of the entries. -/
theorem blob_meta_data_eq (view : MetaView database.BlobMetaEntry)
    (heq : HashMapEqSpec view CoreCmpPartialEqBlobMetaEntry) (a b : database.BlobMetaData) :
    ∃ r, blobMetaDataEq a b = ok r ∧
      (r = true ↔ ∀ k, (view a.data k = none ∧ view b.data k = none) ∨
        ∃ x y, view a.data k = some x ∧ view b.data k = some y ∧ x = y) := by
  sorry

/-- conditional: `encrypted_by` never fails. It returns `Some v` exactly when the number 0 holds the
entry `EncryptedBy v`, and `None` otherwise (no entry, or an entry of another variant).
Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_encrypted_by (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdEncryptedBy self = ok r ∧
      ∀ v, r = some v ↔ view self.data 0#i64 = some (.EncryptedBy v) := by
  sorry

/-- conditional: `salt` never fails. It returns `Some v` exactly when the number 1 holds the entry
`Salt v`, and `None` otherwise (no entry, or an entry of another variant). Hypothesis:
`HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_salt (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdSalt self = ok r ∧
      ∀ v, r = some v ↔ view self.data 1#i64 = some (.Salt v) := by
  sorry

/-- conditional: `iv` never fails. It returns `Some v` exactly when the number 2 holds the entry `Iv
v`, and `None` otherwise (no entry, or an entry of another variant). Hypothesis:
`HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_iv (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdIv self = ok r ∧
      ∀ v, r = some v ↔ view self.data 2#i64 = some (.Iv v) := by
  sorry

/-- conditional: `aead_tag` never fails. It returns `Some v` exactly when the number 3 holds the
entry `AeadTag v`, and `None` otherwise (no entry, or an entry of another variant). Hypothesis:
`HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_aead_tag (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdAeadTag self = ok r ∧
      ∀ v, r = some v ↔ view self.data 3#i64 = some (.AeadTag v) := by
  sorry

/-- conditional: `km_uuid` never fails. It returns `Some v` exactly when the number 4 holds the
entry `KmUuid v`, and `None` otherwise (no entry, or an entry of another variant). Hypothesis:
`HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_km_uuid (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdKmUuid self = ok r ∧
      ∀ v, r = some v ↔ view self.data 4#i64 = some (.KmUuid v) := by
  sorry

/-- conditional: `public_key` never fails. It returns `Some v` exactly when the number 5 holds the
entry `PublicKey v`, and `None` otherwise (no entry, or an entry of another variant).
Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_public_key (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdPublicKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 5#i64 = some (.PublicKey v) := by
  sorry

/-- conditional: `max_boot_level` never fails. It returns `Some v` exactly when the number 6 holds
the entry `MaxBootLevel v`, and `None` otherwise (no entry, or an entry of another variant).
Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem blob_meta_data_max_boot_level (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdMaxBootLevel self = ok r ∧
      ∀ v, r = some v ↔ view self.data 6#i64 = some (.MaxBootLevel v) := by
  sorry
