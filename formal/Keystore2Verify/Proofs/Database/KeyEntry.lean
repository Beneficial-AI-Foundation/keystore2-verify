import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.KeyEntry.Insts
open CoreDefaultDefault renaming default → keyEntryDefault
open CoreCmpPartialEqKeyEntry renaming eq → keyEntryEq
open database.KeyEntry.impl renaming id → keyEntryId
open database.KeyEntry.impl renaming key_blob_info → keyEntryKeyBlobInfo
open database.KeyEntry renaming take_key_blob_info → keyEntryTakeKeyBlobInfo
open database.KeyEntry.impl renaming cert → keyEntryCert
open database.KeyEntry renaming take_cert → keyEntryTakeCert
open database.KeyEntry renaming take_cert_chain → keyEntryTakeCertChain
open database.KeyEntry.impl renaming km_uuid → keyEntryKmUuid
open database.KeyEntry renaming into_key_parameters → keyEntryIntoKeyParameters
open database.KeyEntry.impl renaming metadata → keyEntryMetadata
open database.KeyEntry.impl renaming pure_cert → keyEntryPureCert
open database.KeyEntry renaming is_attested → keyEntryIsAttested
open database.BlobMetaData.Insts renaming CoreCmpPartialEqBlobMetaData → blobMetaDataEq
open database.KeyMetaData.Insts renaming CoreCmpPartialEqKeyMetaData.eq → keyMetaDataEq

/-- conditional: `default` never fails. It returns the entry with id 0, no key blob, no
certificate, no certificate chain, the all-zero KeyMint uuid, no key parameters, empty metadata and
`pure_cert` false. Hypotheses: `OptionDefaultSpec` for the key blob and for the certificate,
`VecDefaultSpec` for the key parameters, and `HashMapDefaultSpec` for the view `view`
of the metadata map. -/
theorem key_entry_default (view : MetaView database.KeyMetaEntry)
    (hblob : OptionDefaultSpec (alloc.vec.Vec Std.U8 × database.BlobMetaData))
    (hcert : OptionDefaultSpec (alloc.vec.Vec Std.U8))
    (hparams : VecDefaultSpec key_parameter.KeyParameter)
    (hmap : HashMapDefaultSpec database.KeyMetaEntry view) :
    ∃ e, keyEntryDefault = ok e ∧ e.id.val = 0 ∧ e.key_blob_info = none ∧ e.cert = none ∧
      e.cert_chain = none ∧ e.km_uuid.val = List.replicate 16 (0#u8) ∧ e.parameters.val = [] ∧
      (∀ k, view e.metadata.data k = none) ∧ e.pure_cert = false := by
  sorry

/-- exact: `eq` returns `false` when the ids differ, and when the ids are equal but `pure_cert`
differs. In the derived implementation that was translated, these two checks come first (the Rust
source declares `pure_cert` last), and the comparison of the other fields is not reached. -/
theorem key_entry_eq_id_pure (a b : database.KeyEntry) :
    (a.id ≠ b.id → keyEntryEq a b = ok false) ∧
    (a.id = b.id → a.pure_cert ≠ b.pure_cert → keyEntryEq a b = ok false) := by
  sorry

/-- conditional: the comparison of the key blobs (`blobInfoEq`) is the third check. Hypotheses:
`id` and `pure_cert` are equal. If the comparison fails, `eq` fails with the same failure, and if
it returns `false`, `eq` returns `false`. -/
theorem key_entry_eq_blob (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert) :
    (∀ f, blobInfoEq a.key_blob_info b.key_blob_info = fail f → keyEntryEq a b = fail f) ∧
    (blobInfoEq a.key_blob_info b.key_blob_info = ok false → keyEntryEq a b = ok false) := by
  sorry

/-- conditional: the key blob check when a key blob is absent. If exactly one of the two entries
has a key blob, `eq` returns `false`. If neither has one, the comparison of the key blobs returns
`true`. Hypotheses: `id` and `pure_cert` are equal, and `OptionEqSpec` for the pair of a key blob
and its metadata (assumption about `Option::eq`). -/
theorem key_entry_eq_blob_absent (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hopt : OptionEqSpec (Pair.Insts.CoreCmpPartialEqPair
      (core.cmp.PartialEqVec core.cmp.PartialEqU8) blobMetaDataEq)) :
    (a.key_blob_info.isSome ≠ b.key_blob_info.isSome → keyEntryEq a b = ok false) ∧
    (a.key_blob_info = none → b.key_blob_info = none →
      blobInfoEq a.key_blob_info b.key_blob_info = ok true) := by
  sorry

/-- conditional: the next checks compare the certificate, the certificate chain and the KeyMint
uuid. Each returns `false` from `eq` when its field differs and the earlier checks passed.
Hypotheses: `id` and `pure_cert` are equal, the comparison of the key blobs returned `true`, and
`OptionEqSpec` for byte vectors (assumption about `Option::eq`). -/
theorem key_entry_eq_certs (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hkb : blobInfoEq a.key_blob_info b.key_blob_info = ok true)
    (hopt : OptionEqSpec (core.cmp.PartialEqVec core.cmp.PartialEqU8)) :
    (a.cert ≠ b.cert → keyEntryEq a b = ok false) ∧
    (a.cert = b.cert → a.cert_chain ≠ b.cert_chain → keyEntryEq a b = ok false) ∧
    (a.cert = b.cert → a.cert_chain = b.cert_chain → a.km_uuid ≠ b.km_uuid →
      keyEntryEq a b = ok false) := by
  sorry

/-- conditional: the comparison of the key parameters (`keyParametersEq`) follows. If it fails,
`eq` fails with the same failure, and if it returns `false`, `eq` returns `false`. Hypotheses:
the earlier fields are equal (`id`, `pure_cert`, key blob by `blobInfoEq`, certificate,
certificate chain, uuid), and `OptionEqSpec` for byte vectors. -/
theorem key_entry_eq_parameters (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hkb : blobInfoEq a.key_blob_info b.key_blob_info = ok true)
    (hopt : OptionEqSpec (core.cmp.PartialEqVec core.cmp.PartialEqU8))
    (hcert : a.cert = b.cert) (hchain : a.cert_chain = b.cert_chain)
    (huuid : a.km_uuid = b.km_uuid) :
    (∀ f, keyParametersEq a.parameters b.parameters = fail f → keyEntryEq a b = fail f) ∧
    (keyParametersEq a.parameters b.parameters = ok false → keyEntryEq a b = ok false) := by
  sorry

/-- conditional: the comparison of the metadata is the last check, and its result is the result of
`eq`. If it fails, `eq` fails with the same failure. Hypotheses: the earlier fields are equal
(as for `key_entry_eq_parameters`), the comparison of the key parameters returned `true`, and
`OptionEqSpec` for byte vectors. -/
theorem key_entry_eq_metadata (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hkb : blobInfoEq a.key_blob_info b.key_blob_info = ok true)
    (hopt : OptionEqSpec (core.cmp.PartialEqVec core.cmp.PartialEqU8))
    (hcert : a.cert = b.cert) (hchain : a.cert_chain = b.cert_chain)
    (huuid : a.km_uuid = b.km_uuid)
    (hp : keyParametersEq a.parameters b.parameters = ok true) :
    (∀ f, keyMetaDataEq a.metadata b.metadata = fail f → keyEntryEq a b = fail f) ∧
    (∀ m, keyMetaDataEq a.metadata b.metadata = ok m → keyEntryEq a b = ok m) := by
  sorry

/-- exact: `id` never fails and returns the `id` field. -/
theorem key_entry_id (e : database.KeyEntry) : keyEntryId e = ok e.id := by
  sorry

/-- exact: `key_blob_info` never fails and returns the `key_blob_info` field. -/
theorem key_entry_key_blob_info (e : database.KeyEntry) :
    keyEntryKeyBlobInfo e = ok e.key_blob_info := by
  sorry

/-- exact: `take_key_blob_info` never fails. It returns the key blob and leaves `None` in its
place. Nothing else changes. -/
theorem key_entry_take_key_blob_info (e : database.KeyEntry) :
    keyEntryTakeKeyBlobInfo e = ok (e.key_blob_info, { e with key_blob_info := none }) := by
  sorry

/-- exact: `cert` never fails and returns the `cert` field. -/
theorem key_entry_cert (e : database.KeyEntry) : keyEntryCert e = ok e.cert := by
  sorry

/-- exact: `take_cert` never fails. It returns the certificate and leaves `None` in its place.
Nothing else changes. -/
theorem key_entry_take_cert (e : database.KeyEntry) :
    keyEntryTakeCert e = ok (e.cert, { e with cert := none }) := by
  sorry

/-- exact: `take_cert_chain` never fails. It returns the certificate chain and leaves `None` in
its place. Nothing else changes. -/
theorem key_entry_take_cert_chain (e : database.KeyEntry) :
    keyEntryTakeCertChain e = ok (e.cert_chain, { e with cert_chain := none }) := by
  sorry

/-- exact: `km_uuid` never fails and returns the `km_uuid` field. -/
theorem key_entry_km_uuid (e : database.KeyEntry) : keyEntryKmUuid e = ok e.km_uuid := by
  sorry

/-- exact: `into_key_parameters` never fails and returns the `parameters` field. -/
theorem key_entry_into_key_parameters (e : database.KeyEntry) :
    keyEntryIntoKeyParameters e = ok e.parameters := by
  sorry

/-- exact: `metadata` never fails and returns the `metadata` field. -/
theorem key_entry_metadata (e : database.KeyEntry) : keyEntryMetadata e = ok e.metadata := by
  sorry

/-- exact: `pure_cert` never fails and returns the `pure_cert` field. -/
theorem key_entry_pure_cert (e : database.KeyEntry) : keyEntryPureCert e = ok e.pure_cert := by
  sorry

/-- exact: `is_attested` never fails. It returns `true` exactly when the entry has a certificate
chain. -/
theorem key_entry_is_attested (e : database.KeyEntry) :
    keyEntryIsAttested e = ok e.cert_chain.isSome := by
  sorry
