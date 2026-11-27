import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb
import Keystore2Verify.Specs.Defs.Permission

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open Keystore2Verify.Permission (AnyhowStrCtxLaw)

/-! The four reads of this method come in this order: the metadata, the blobs, the parameters and
the uuid. In the Rust source an error returns at once, and no later read is called. Each theorem
takes the outcomes of the reads before it as hypotheses, and the `context` assumption at each of the
four calls. The reads are inline hypotheses: three of them are not translated, and the fourth,
`get_key_km_uuid`, reads the database. -/

/-- conditional: if the four reads return `Ok`, the result is `Ok` of the key entry with the
id `key_id`, the blob information, the certificate and the certificate chain of the blob read,
the uuid, the parameters and the metadata. The entry is a pure certificate exactly when the blob
read says that there is no key blob. Hypotheses: the reads return `m`, `(has, kbi, cert, chain)`,
`ps` and `u`; the `context` assumption at each call. -/
theorem load_key_components_ok (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (m : database.KeyMetaData) (has : Bool)
    (kbi : Option ((alloc.vec.Vec Std.U8) × database.BlobMetaData))
    (cert chain : Option (alloc.vec.Vec Std.U8))
    (ps : alloc.vec.Vec key_parameter.KeyParameter) (u : database.Uuid)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Ok m))
    (hb : database.KeystoreDB.load_blob_components key_id load_bits tx =
      ok (.Ok (has, kbi, cert, chain)))
    (hp : database.KeystoreDB.load_key_parameters key_id tx = ok (.Ok ps))
    (hu : database.KeystoreDB.get_key_km_uuid tx key_id = ok (.Ok u))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData)
    (h2 : AnyhowStrCtxLaw root BlobComponents)
    (h3 : AnyhowStrCtxLaw root (alloc.vec.Vec key_parameter.KeyParameter))
    (h4 : AnyhowStrCtxLaw root database.Uuid) :
    database.KeystoreDB.load_key_components tx load_bits key_id =
      ok (.Ok { id := key_id, key_blob_info := kbi, cert := cert, cert_chain := chain,
                km_uuid := u, parameters := ps, metadata := m, pure_cert := (¬ has) }) := by
  sorry

/-- conditional: if the metadata read returns an error `x`, the result is an `Err e` with the
same root cause as `x`. In the Rust source no other read is called. Hypotheses: the metadata
read returns `Err x`; the `context` assumption at the first call. -/
theorem load_key_components_metadata_error (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (x : anyhow.Error)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Err x))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData) :
    ∃ e, database.KeystoreDB.load_key_components tx load_bits key_id = ok (.Err e) ∧
      root e = root x := by
  sorry

/-- conditional: if the metadata read returns `Ok m` and the blob read returns an error `x`, the
result is an `Err e` with the same root cause as `x`. In the Rust source the parameters and the uuid
are not read. Hypotheses: the two reads return as said; the `context` assumptions at the first two
calls. -/
theorem load_key_components_blob_error (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (m : database.KeyMetaData) (x : anyhow.Error)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Ok m))
    (hb : database.KeystoreDB.load_blob_components key_id load_bits tx = ok (.Err x))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData)
    (h2 : AnyhowStrCtxLaw root BlobComponents) :
    ∃ e, database.KeystoreDB.load_key_components tx load_bits key_id = ok (.Err e) ∧
      root e = root x := by
  sorry

/-- conditional: if the metadata and blob reads return `Ok` and the parameter read returns an error
`x`, the result is an `Err e` with the same root cause as `x`. In the Rust source the uuid is
not read. Hypotheses: the three reads return as said; the `context` assumptions at the first three
calls. -/
theorem load_key_components_parameters_error (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (m : database.KeyMetaData) (blobs : BlobComponents) (x : anyhow.Error)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Ok m))
    (hb : database.KeystoreDB.load_blob_components key_id load_bits tx = ok (.Ok blobs))
    (hp : database.KeystoreDB.load_key_parameters key_id tx = ok (.Err x))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData)
    (h2 : AnyhowStrCtxLaw root BlobComponents)
    (h3 : AnyhowStrCtxLaw root (alloc.vec.Vec key_parameter.KeyParameter)) :
    ∃ e, database.KeystoreDB.load_key_components tx load_bits key_id = ok (.Err e) ∧
      root e = root x := by
  sorry

/-- conditional: if the first three reads return `Ok` and the uuid read returns an error `x`, the
result is an `Err e` with the same root cause as `x`. Hypotheses: the four reads return as said;
the `context` assumption at each call. -/
theorem load_key_components_uuid_error (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (m : database.KeyMetaData) (blobs : BlobComponents)
    (ps : alloc.vec.Vec key_parameter.KeyParameter) (x : anyhow.Error)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Ok m))
    (hb : database.KeystoreDB.load_blob_components key_id load_bits tx = ok (.Ok blobs))
    (hp : database.KeystoreDB.load_key_parameters key_id tx = ok (.Ok ps))
    (hu : database.KeystoreDB.get_key_km_uuid tx key_id = ok (.Err x))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData)
    (h2 : AnyhowStrCtxLaw root BlobComponents)
    (h3 : AnyhowStrCtxLaw root (alloc.vec.Vec key_parameter.KeyParameter))
    (h4 : AnyhowStrCtxLaw root database.Uuid) :
    ∃ e, database.KeystoreDB.load_key_components tx load_bits key_id = ok (.Err e) ∧
      root e = root x := by
  sorry
