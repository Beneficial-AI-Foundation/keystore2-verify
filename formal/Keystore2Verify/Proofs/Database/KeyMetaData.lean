import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.KeyMetaEntry renaming db_tag → keyMetaEntryDbTag
open database.KeyMetaData renaming add → keyMetaDataAdd
open database.KeyMetaData.Insts
open database.KeyMetaEntry.Insts
open CoreDefaultDefault renaming default → keyMetaDataDefault
open CoreCmpPartialEqKeyMetaData renaming eq → keyMetaDataEq
open database.KeyMetaData renaming creation_date → kmdCreationDate
open database.KeyMetaData renaming attestation_expiration_date → kmdAttestationExpirationDate
open database.KeyMetaData renaming attestation_maced_public_key → kmdAttestationMacedPublicKey
open database.KeyMetaData renaming attestation_raw_pub_key → kmdAttestationRawPubKey
open database.KeyMetaData renaming sec1_public_key → kmdSec1PublicKey

/-- conditional: `add` never fails. The new map holds the entry under its number (the result of
`db_tag`), and every other number keeps its entry. An earlier entry of the same variant is
replaced. Hypothesis: `HashMapInsertSpec` (assumption about `HashMap::insert`) for the view
`view`. -/
theorem key_meta_data_add (view : MetaView database.KeyMetaEntry)
    (hins : HashMapInsertSpec view) (self : database.KeyMetaData)
    (e : database.KeyMetaEntry) :
    ∃ t md, keyMetaEntryDbTag e = ok t ∧ keyMetaDataAdd self e = ok md ∧
      view md.data t = some e ∧ ∀ j, j ≠ t → view md.data j = view self.data j := by
  sorry

/-- conditional: `default` never fails and returns an empty map. Hypothesis: `HashMapDefaultSpec`
for the view `view`. -/
theorem key_meta_data_default (view : MetaView database.KeyMetaEntry)
    (hdef : HashMapDefaultSpec database.KeyMetaEntry view) :
    ∃ md, keyMetaDataDefault = ok md ∧ ∀ k, view md.data k = none := by
  sorry

/-- conditional: `eq` never fails. It returns `true` exactly when both maps have the same numbers,
with equal entries under each. Hypothesis: `HashMapEqSpec` for the view `view` and the derived
`eq` of the entries. -/
theorem key_meta_data_eq (view : MetaView database.KeyMetaEntry)
    (heq : HashMapEqSpec view CoreCmpPartialEqKeyMetaEntry) (a b : database.KeyMetaData) :
    ∃ r, keyMetaDataEq a b = ok r ∧
      (r = true ↔ ∀ k, (view a.data k = none ∧ view b.data k = none) ∨
        ∃ x y, view a.data k = some x ∧ view b.data k = some y ∧ x = y) := by
  sorry

/-- conditional: `creation_date` never fails. It returns `Some v` exactly when the number 0 holds
the entry `CreationDate v`, and `None` otherwise (no entry, or an entry of another variant).
Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem key_meta_data_creation_date (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdCreationDate self = ok r ∧
      ∀ v, r = some v ↔ view self.data 0#i64 = some (.CreationDate v) := by
  sorry

/-- conditional: `attestation_expiration_date` never fails. It returns `Some v` exactly when the
number 1 holds the entry `AttestationExpirationDate v`, and `None` otherwise (no entry, or an
entry of another variant). Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for
the view `view`. -/
theorem key_meta_data_attestation_expiration_date (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdAttestationExpirationDate self = ok r ∧
      ∀ v, r = some v ↔ view self.data 1#i64 = some (.AttestationExpirationDate v) := by
  sorry

/-- conditional: `attestation_maced_public_key` never fails. It returns `Some v` exactly when the
number 2 holds the entry `AttestationMacedPublicKey v`, and `None` otherwise (no entry, or an
entry of another variant). Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for
the view `view`. -/
theorem key_meta_data_attestation_maced_public_key (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdAttestationMacedPublicKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 2#i64 = some (.AttestationMacedPublicKey v) := by
  sorry

/-- conditional: `attestation_raw_pub_key` never fails. It returns `Some v` exactly when the number
3 holds the entry `AttestationRawPubKey v`, and `None` otherwise (no entry, or an entry of
another variant). Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for the view
`view`. -/
theorem key_meta_data_attestation_raw_pub_key (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdAttestationRawPubKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 3#i64 = some (.AttestationRawPubKey v) := by
  sorry

/-- conditional: `sec1_public_key` never fails. It returns `Some v` exactly when the number 4 holds
the entry `Sec1PublicKey v`, and `None` otherwise (no entry, or an entry of another variant).
Hypothesis: `HashMapGetSpec` (assumption about `HashMap::get`) for the view `view`. -/
theorem key_meta_data_sec1_public_key (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdSec1PublicKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 4#i64 = some (.Sec1PublicKey v) := by
  sorry
