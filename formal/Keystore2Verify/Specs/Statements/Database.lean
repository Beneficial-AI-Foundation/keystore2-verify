import Keystore2Verify.Proofs.Database.TransactionBehavior
import Keystore2Verify.Proofs.Database.KeyMetaEntry
import Keystore2Verify.Proofs.Database.KeyMetaData
import Keystore2Verify.Proofs.Database.BlobMetaEntry
import Keystore2Verify.Proofs.Database.BlobMetaData
import Keystore2Verify.Proofs.Database.KeyType
import Keystore2Verify.Proofs.Database.Uuid
import Keystore2Verify.Proofs.Database.EncryptedBy
import Keystore2Verify.Proofs.Database.DateTime
import Keystore2Verify.Proofs.Database.DateTimeError
import Keystore2Verify.Proofs.Database.KeyLifeCycle
import Keystore2Verify.Proofs.Database.BlobState
import Keystore2Verify.Proofs.Database.KeyEntryLoadBits
import Keystore2Verify.Proofs.Database.KeyIdGuard
import Keystore2Verify.Proofs.Database.CertificateInfo
import Keystore2Verify.Proofs.Database.KeyEntry
import Keystore2Verify.Proofs.Database.SubComponentType
import Keystore2Verify.Proofs.Database.DoGc
import Keystore2Verify.Proofs.Database.BootTime
import Keystore2Verify.Proofs.Database.AuthTokenEntry

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section TransactionBehavior
open database.TransactionBehavior.Insts.CoreCloneClone renaming clone → txBehaviorClone
open rusqlite.transaction.TransactionBehavior.Insts.CoreConvertFromTransactionBehavior
  renaming «from» → rusqliteFromTxBehavior

recall transaction_behavior_clone (x : database.TransactionBehavior) :
    txBehaviorClone x = ok x

recall transaction_behavior_from_deferred :
    rusqliteFromTxBehavior .Deferred = ok .Deferred

recall transaction_behavior_from_immediate (s : Str) :
    rusqliteFromTxBehavior (.Immediate s) = ok .Immediate

end TransactionBehavior

section KeyMetaEntry
open database.KeyMetaEntry renaming db_tag → keyMetaEntryDbTag
open database.KeyMetaEntry renaming new_from_sql → keyMetaEntryNewFromSql
open database.utils.SqlField renaming get → sqlFieldGet
open database.DateTime.Insts renaming RusqliteTypesFrom_sqlFromSql → dateTimeFromSql
open alloc.vec.VecU8.Insts renaming RusqliteTypesFrom_sqlFromSql → vecU8FromSql
open database.KeyMetaEntry.new_from_sql.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce0
open database.KeyMetaEntry.new_from_sql.closure_1.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce1
open database.KeyMetaEntry.new_from_sql.closure_2.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce2
open database.KeyMetaEntry.new_from_sql.closure_3.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce3
open database.KeyMetaEntry.new_from_sql.closure_4.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce4
open database.KeyMetaEntry.Insts
open CoreCmpPartialEqKeyMetaEntry renaming eq → keyMetaEntryEq
open CoreCmpOrd renaming cmp → keyMetaEntryCmpFn
open CoreCmpPartialOrdKeyMetaEntry renaming partial_cmp → keyMetaEntryPartialCmp

recall key_meta_entry_db_tag :
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.CreationDate x) = ok 0#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.AttestationExpirationDate x) = ok 1#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.AttestationMacedPublicKey x) = ok 2#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.AttestationRawPubKey x) = ok 3#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.Sec1PublicKey x) = ok 4#i64)

recall key_meta_entry_new_from_sql_creation_date
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.DateTime) rootSql root
      fnOnce0)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet dateTimeFromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 0#i64 data = ok (.Ok (.CreationDate v))) ∧
    (∀ e, sqlFieldGet dateTimeFromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 0#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall key_meta_entry_new_from_sql_attestation_expiration_date
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.DateTime) rootSql root
      fnOnce1)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet dateTimeFromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 1#i64 data = ok (.Ok (.AttestationExpirationDate v))) ∧
    (∀ e, sqlFieldGet dateTimeFromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 1#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall key_meta_entry_new_from_sql_attestation_maced_public_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce2)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 2#i64 data = ok (.Ok (.AttestationMacedPublicKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 2#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall key_meta_entry_new_from_sql_attestation_raw_pub_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce3)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 3#i64 data = ok (.Ok (.AttestationRawPubKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 3#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall key_meta_entry_new_from_sql_sec1_public_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce4)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 4#i64 data = ok (.Ok (.Sec1PublicKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 4#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall key_meta_entry_new_from_sql_unknown_tag
    (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hnew : AnyhowAdhocNewSpec root)
    (hmu : AnyhowMustUseSpec)
    (tag : Std.I64) (data : database.utils.SqlField) (h : tag.val < 0 ∨ 4 < tag.val) :
    ∃ e, keyMetaEntryNewFromSql tag data = ok (.Err e) ∧ root e = ErrRoot.other

recall key_meta_entry_eq (a b : database.KeyMetaEntry) :
    ∃ r, keyMetaEntryEq a b = ok r ∧ (r = true ↔ a = b)

recall key_meta_entry_cmp_variants (a b : database.KeyMetaEntry)
    (h : keyMetaEntryRank a ≠ keyMetaEntryRank b) :
    keyMetaEntryCmpFn a b = ok (compare (keyMetaEntryRank a) (keyMetaEntryRank b))

recall key_meta_entry_cmp (h : VecU8CmpSpec)
    (a b : database.KeyMetaEntry) :
    keyMetaEntryCmpFn a b = ok (keyMetaEntryCmp a b)

recall key_meta_entry_partial_cmp (a b : database.KeyMetaEntry) :
    (∀ o, keyMetaEntryCmpFn a b = ok o → keyMetaEntryPartialCmp a b = ok (some o)) ∧
    (∀ f, keyMetaEntryCmpFn a b = fail f → keyMetaEntryPartialCmp a b = fail f)

end KeyMetaEntry

section KeyMetaData
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

recall key_meta_data_add (view : MetaView database.KeyMetaEntry)
    (hins : HashMapInsertSpec view) (self : database.KeyMetaData)
    (e : database.KeyMetaEntry) :
    ∃ t md, keyMetaEntryDbTag e = ok t ∧ keyMetaDataAdd self e = ok md ∧
      view md.data t = some e ∧ ∀ j, j ≠ t → view md.data j = view self.data j

recall key_meta_data_default (view : MetaView database.KeyMetaEntry)
    (hdef : HashMapDefaultSpec database.KeyMetaEntry view) :
    ∃ md, keyMetaDataDefault = ok md ∧ ∀ k, view md.data k = none

recall key_meta_data_eq (view : MetaView database.KeyMetaEntry)
    (heq : HashMapEqSpec view CoreCmpPartialEqKeyMetaEntry) (a b : database.KeyMetaData) :
    ∃ r, keyMetaDataEq a b = ok r ∧
      (r = true ↔ ∀ k, (view a.data k = none ∧ view b.data k = none) ∨
        ∃ x y, view a.data k = some x ∧ view b.data k = some y ∧ x = y)

recall key_meta_data_creation_date (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdCreationDate self = ok r ∧
      ∀ v, r = some v ↔ view self.data 0#i64 = some (.CreationDate v)

recall key_meta_data_attestation_expiration_date (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdAttestationExpirationDate self = ok r ∧
      ∀ v, r = some v ↔ view self.data 1#i64 = some (.AttestationExpirationDate v)

recall key_meta_data_attestation_maced_public_key (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdAttestationMacedPublicKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 2#i64 = some (.AttestationMacedPublicKey v)

recall key_meta_data_attestation_raw_pub_key (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdAttestationRawPubKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 3#i64 = some (.AttestationRawPubKey v)

recall key_meta_data_sec1_public_key (view : MetaView database.KeyMetaEntry)
    (hget : HashMapGetSpec view) (self : database.KeyMetaData) :
    ∃ r, kmdSec1PublicKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 4#i64 = some (.Sec1PublicKey v)

end KeyMetaData

section BlobMetaEntry
open database.BlobMetaEntry renaming db_tag → blobMetaEntryDbTag
open database.BlobMetaEntry renaming new_from_sql → blobMetaEntryNewFromSql
open database.utils.SqlField renaming get → sqlFieldGet
open database.EncryptedBy.Insts renaming RusqliteTypesFrom_sqlFromSql → encryptedByFromSql
open I32.Insts renaming RusqliteTypesFrom_sqlFromSql → i32FromSql
open database.Uuid.Insts renaming RusqliteTypesFrom_sqlFromSql → uuidFromSql
open alloc.vec.VecU8.Insts renaming RusqliteTypesFrom_sqlFromSql → vecU8FromSql
open database.BlobMetaEntry.new_from_sql.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce0
open database.BlobMetaEntry.new_from_sql.closure_1.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce1
open database.BlobMetaEntry.new_from_sql.closure_2.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce2
open database.BlobMetaEntry.new_from_sql.closure_3.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce3
open database.BlobMetaEntry.new_from_sql.closure_4.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce4
open database.BlobMetaEntry.new_from_sql.closure_5.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce5
open database.BlobMetaEntry.new_from_sql.closure_6.Insts renaming
  CoreOpsFunctionFnOnceTupleString → fnOnce6
open database.BlobMetaEntry.Insts
open CoreCmpPartialEqBlobMetaEntry renaming eq → blobMetaEntryEq
open CoreCmpOrd renaming cmp → blobMetaEntryCmpFn
open CoreCmpPartialOrdBlobMetaEntry renaming partial_cmp → blobMetaEntryPartialCmp

recall blob_meta_entry_db_tag :
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.EncryptedBy x) = ok 0#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.Salt x) = ok 1#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.Iv x) = ok 2#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.AeadTag x) = ok 3#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.KmUuid x) = ok 4#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.PublicKey x) = ok 5#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.MaxBootLevel x) = ok 6#i64)

recall blob_meta_entry_new_from_sql_encrypted_by
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.EncryptedBy) rootSql root
      fnOnce0)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet encryptedByFromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 0#i64 data = ok (.Ok (.EncryptedBy v))) ∧
    (∀ e, sqlFieldGet encryptedByFromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 0#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_salt
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce1)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 1#i64 data = ok (.Ok (.Salt v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 1#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_iv
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce2)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 2#i64 data = ok (.Ok (.Iv v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 2#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_aead_tag
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce3)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 3#i64 data = ok (.Ok (.AeadTag v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 3#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_km_uuid
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.Uuid) rootSql root
      fnOnce4)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet uuidFromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 4#i64 data = ok (.Ok (.KmUuid v))) ∧
    (∀ e, sqlFieldGet uuidFromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 4#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_public_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce5)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 5#i64 data = ok (.Ok (.PublicKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 5#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_max_boot_level
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := Std.I32) rootSql root
      fnOnce6)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet i32FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 6#i64 data = ok (.Ok (.MaxBootLevel v))) ∧
    (∀ e, sqlFieldGet i32FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 6#i64 data = ok (.Err e') ∧ root e' = rootSql e)

recall blob_meta_entry_new_from_sql_unknown_tag
    (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hnew : AnyhowAdhocNewSpec root)
    (hmu : AnyhowMustUseSpec)
    (tag : Std.I64) (data : database.utils.SqlField) (h : tag.val < 0 ∨ 6 < tag.val) :
    ∃ e, blobMetaEntryNewFromSql tag data = ok (.Err e) ∧ root e = ErrRoot.other

recall blob_meta_entry_eq (a b : database.BlobMetaEntry) :
    ∃ r, blobMetaEntryEq a b = ok r ∧ (r = true ↔ a = b)

recall blob_meta_entry_cmp_variants (a b : database.BlobMetaEntry)
    (h : blobMetaEntryRank a ≠ blobMetaEntryRank b) :
    blobMetaEntryCmpFn a b = ok (compare (blobMetaEntryRank a) (blobMetaEntryRank b))

recall blob_meta_entry_cmp (h : VecU8CmpSpec) (harr : ArrayU8Cmp16Spec)
    (a b : database.BlobMetaEntry) :
    blobMetaEntryCmpFn a b = ok (blobMetaEntryCmp a b)

recall blob_meta_entry_partial_cmp (a b : database.BlobMetaEntry) :
    (∀ o, blobMetaEntryCmpFn a b = ok o → blobMetaEntryPartialCmp a b = ok (some o)) ∧
    (∀ f, blobMetaEntryCmpFn a b = fail f → blobMetaEntryPartialCmp a b = fail f)

end BlobMetaEntry

section BlobMetaData
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

recall blob_meta_data_add (view : MetaView database.BlobMetaEntry)
    (hins : HashMapInsertSpec view) (self : database.BlobMetaData)
    (e : database.BlobMetaEntry) :
    ∃ t md, blobMetaEntryDbTag e = ok t ∧ blobMetaDataAdd self e = ok md ∧
      view md.data t = some e ∧ ∀ j, j ≠ t → view md.data j = view self.data j

recall blob_meta_data_default (view : MetaView database.BlobMetaEntry)
    (hdef : HashMapDefaultSpec database.BlobMetaEntry view) :
    ∃ md, blobMetaDataDefault = ok md ∧ ∀ k, view md.data k = none

recall blob_meta_data_eq (view : MetaView database.BlobMetaEntry)
    (heq : HashMapEqSpec view CoreCmpPartialEqBlobMetaEntry) (a b : database.BlobMetaData) :
    ∃ r, blobMetaDataEq a b = ok r ∧
      (r = true ↔ ∀ k, (view a.data k = none ∧ view b.data k = none) ∨
        ∃ x y, view a.data k = some x ∧ view b.data k = some y ∧ x = y)

recall blob_meta_data_encrypted_by (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdEncryptedBy self = ok r ∧
      ∀ v, r = some v ↔ view self.data 0#i64 = some (.EncryptedBy v)

recall blob_meta_data_salt (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdSalt self = ok r ∧
      ∀ v, r = some v ↔ view self.data 1#i64 = some (.Salt v)

recall blob_meta_data_iv (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdIv self = ok r ∧
      ∀ v, r = some v ↔ view self.data 2#i64 = some (.Iv v)

recall blob_meta_data_aead_tag (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdAeadTag self = ok r ∧
      ∀ v, r = some v ↔ view self.data 3#i64 = some (.AeadTag v)

recall blob_meta_data_km_uuid (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdKmUuid self = ok r ∧
      ∀ v, r = some v ↔ view self.data 4#i64 = some (.KmUuid v)

recall blob_meta_data_public_key (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdPublicKey self = ok r ∧
      ∀ v, r = some v ↔ view self.data 5#i64 = some (.PublicKey v)

recall blob_meta_data_max_boot_level (view : MetaView database.BlobMetaEntry)
    (hget : HashMapGetSpec view) (self : database.BlobMetaData) :
    ∃ r, bmdMaxBootLevel self = ok r ∧
      ∀ v, r = some v ↔ view self.data 6#i64 = some (.MaxBootLevel v)

end BlobMetaData

section KeyType
open database.KeyType.Insts
open CoreCloneClone renaming clone → keyTypeClone
open CoreCmpPartialEqKeyType renaming eq → keyTypeEq
open CoreCmpOrd renaming cmp → keyTypeCmp
open CoreCmpPartialOrdKeyType renaming partial_cmp → keyTypePartialCmp

recall key_type_clone (x : database.KeyType) : keyTypeClone x = ok x

recall key_type_eq (a b : database.KeyType) :
    ∃ r, keyTypeEq a b = ok r ∧ (r = true ↔ a = b)

recall key_type_cmp (a b : database.KeyType) :
    keyTypeCmp a b = ok (compare (keyTypeRank a) (keyTypeRank b))

recall key_type_partial_cmp (a b : database.KeyType) :
    keyTypePartialCmp a b = ok (some (compare (keyTypeRank a) (keyTypeRank b)))

end KeyType

section Uuid
open database.Uuid.Insts
open CoreCloneClone renaming clone → uuidClone
open CoreCmpPartialEqUuid renaming eq → uuidEq
open CoreCmpOrd renaming cmp → uuidCmp
open CoreCmpPartialOrdUuid renaming partial_cmp → uuidPartialCmp
open CoreDefaultDefault renaming default → uuidDefault
open CoreOpsDerefDerefArrayU816 renaming deref → uuidDeref
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open CoreConvertFromSecurityLevel renaming «from» → uuidFromSecurityLevel

recall uuid_clone (x : database.Uuid) : uuidClone x = ok x

recall uuid_default :
    ∃ u, uuidDefault = ok u ∧ u.val = List.replicate 16 (0#u8)

recall uuid_eq (a b : database.Uuid) :
    ∃ r, uuidEq a b = ok r ∧ (r = true ↔ a = b)

recall uuid_cmp (h : ArrayU8Cmp16Spec) (a b : database.Uuid) :
    uuidCmp a b = ok (lexCmp a.val b.val)

recall uuid_partial_cmp (h : ArrayU8Cmp16Spec) (a b : database.Uuid) :
    uuidPartialCmp a b = ok (some (lexCmp a.val b.val))

recall uuid_deref (x : database.Uuid) : uuidDeref x = ok x

recall uuid_from_security_level (s : SecurityLevel.SecurityLevel) :
    ∃ u, uuidFromSecurityLevel s = ok u ∧ u.val.length = 16 ∧
      (beNat u.val : Int) = s.val % 2 ^ 128

end Uuid

section EncryptedBy
open database.EncryptedBy.Insts
open CoreCmpPartialEqEncryptedBy renaming eq → encryptedByEq
open CoreCmpOrd renaming cmp → encryptedByCmpFn
open CoreCmpPartialOrdEncryptedBy renaming partial_cmp → encryptedByPartialCmp

recall encrypted_by_eq (a b : database.EncryptedBy) :
    ∃ r, encryptedByEq a b = ok r ∧ (r = true ↔ a = b)

recall encrypted_by_cmp (a b : database.EncryptedBy) :
    encryptedByCmpFn a b = ok (encryptedByCmp a b)

recall encrypted_by_partial_cmp (a b : database.EncryptedBy) :
    encryptedByPartialCmp a b = ok (some (encryptedByCmp a b))

end EncryptedBy

section DateTime
open std.time
open core.time.Duration renaming checked_sub → durationCheckedSub
open database.TryIntoDateTimeSystemTimeDateTimeError.try_into.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleDurationOptionSystemTime → fnOnceSub
open database.TryIntoDateTimeSystemTimeDateTimeError.try_into.closure_1.Insts
  renaming CoreOpsFunctionFnOnceTupleDurationOptionSystemTime → fnOnceAdd
open database.DateTime.Insts
open CoreCloneClone renaming clone → dateTimeClone
open CoreCmpPartialEqDateTime renaming eq → dateTimeEq
open CoreCmpOrd renaming cmp → dateTimeCmp
open CoreCmpPartialOrdDateTime renaming partial_cmp → dateTimePartialCmp
open CoreDefaultDefault renaming default → dateTimeDefault
open CoreConvertTryFromSystemTimeDateTimeError renaming try_from → dateTimeTryFrom
open CoreConvertTryIntoSystemTimeDateTimeError renaming try_into → dateTimeTryInto
open database.DateTime renaming now → dateTimeNow
open database.DateTime renaming from_millis_epoch → dateTimeFromMillis
open database.DateTime renaming to_millis_epoch → dateTimeToMillis

recall date_time_clone (x : database.DateTime) : dateTimeClone x = ok x

recall date_time_default : dateTimeDefault = ok 0#i64

recall date_time_eq (a b : database.DateTime) :
    ∃ r, dateTimeEq a b = ok r ∧ (r = true ↔ a = b)

recall date_time_cmp (a b : database.DateTime) :
    dateTimeCmp a b = ok (compare a.val b.val)

recall date_time_partial_cmp (a b : database.DateTime) :
    dateTimePartialCmp a b = ok (some (compare a.val b.val))

recall date_time_from_millis_epoch (m : Std.I64) : dateTimeFromMillis m = ok m

recall date_time_to_millis_epoch (d : database.DateTime) : dateTimeToMillis d = ok d

recall date_time_try_from_before_epoch (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (t : SystemTime)
    (hneg : nanos t < 0) :
    ∃ e, dateTimeTryFrom t = ok (.Err (.SystemTimeError e))

recall date_time_try_from_ok (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (h0 : 0 ≤ nanos t) (hfit : nanos t / 1000000 ≤ Std.I64.max) :
    ∃ v, dateTimeTryFrom t = ok (.Ok v) ∧ v.val = nanos t / 1000000

recall date_time_try_from_overflow (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (h0 : 0 ≤ nanos t) (hbig : Std.I64.max < nanos t / 1000000) :
    ∃ e, dateTimeTryFrom t = ok (.Err (.TypeConversion e))

recall date_time_now_before_epoch (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (hneg : nanos t < 0) :
    ∃ e, dateTimeNow = ok (.Err (.SystemTimeError e))

recall date_time_now_ok (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (hfit : nanos t / 1000000 ≤ Std.I64.max) :
    ∃ v, dateTimeNow = ok (.Ok v) ∧ v.val = nanos t / 1000000

recall date_time_now_overflow (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hms : DurationAsMillisSpec dnanos)
    (hc : I64TryFromU128Spec) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (hbig : Std.I64.max < nanos t / 1000000) :
    ∃ e, dateTimeNow = ok (.Err (.TypeConversion e))

recall date_time_try_into_before_epoch (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (t : SystemTime)
    (hnow : SystemTime.now = ok t) (hneg : nanos t < 0) (d : database.DateTime) :
    ∃ e, dateTimeTryInto d = ok (.Err (.SystemTimeError e))

recall date_time_try_into_negative (nanos : SystemTime → Int)
    (dnanos : core.time.Duration → Nat) (hep : UnixEpochSpec nanos)
    (hds : DurationSinceSpec nanos dnanos) (hu : U64TryFromI64Spec)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : d.val < 0) :
    ∃ e, dateTimeTryInto d = ok (.Err (.TypeConversion e))

recall date_time_try_into_earlier
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceSub)
    (hsub : SystemTimeCheckedSubSpec nanos dnanos)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hlt : d.val * 1000000 < nanos t)
    (hok : ∀ dd, (dnanos dd : Int) = nanos t - d.val * 1000000 →
      ∃ t', SystemTime.checked_sub t dd = ok (some t')) :
    ∃ t', dateTimeTryInto d = ok (.Ok t') ∧ nanos t' = d.val * 1000000

recall date_time_try_into_not_earlier
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceAdd)
    (hadd : SystemTimeCheckedAddSpec nanos dnanos)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hge : nanos t ≤ d.val * 1000000)
    (hok : ∀ dd, (dnanos dd : Int) = d.val * 1000000 - nanos t →
      ∃ t', SystemTime.checked_add t dd = ok (some t')) :
    ∃ t', dateTimeTryInto d = ok (.Ok t') ∧ nanos t' = d.val * 1000000

recall date_time_try_into_earlier_overflow
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceSub)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hlt : d.val * 1000000 < nanos t)
    (hnone : ∀ dd, (dnanos dd : Int) = nanos t - d.val * 1000000 →
      SystemTime.checked_sub t dd = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic)

recall date_time_try_into_not_earlier_overflow
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hcs : DurationCheckedSubSpec dnanos) (hand : OptionAndThenSpec fnOnceAdd)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hge : nanos t ≤ d.val * 1000000)
    (hnone : ∀ dd, (dnanos dd : Int) = d.val * 1000000 - nanos t →
      SystemTime.checked_add t dd = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic)

recall date_time_try_into_earlier_duration_none
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hand : OptionAndThenSpec fnOnceSub)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hlt : d.val * 1000000 < nanos t)
    (hnone : ∀ a b, dnanos a = nanos t → dnanos b = d.val * 1000000 →
      durationCheckedSub a b = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic)

recall date_time_try_into_not_earlier_duration_none
    (nanos : SystemTime → Int) (dnanos : core.time.Duration → Nat)
    (hep : UnixEpochSpec nanos) (hds : DurationSinceSpec nanos dnanos)
    (hu : U64TryFromI64Spec) (hfm : DurationFromMillisSpec dnanos)
    (hpc : DurationPartialCmpSpec dnanos)
    (hand : OptionAndThenSpec fnOnceAdd)
    (t : SystemTime) (hnow : SystemTime.now = ok t) (h0 : 0 ≤ nanos t)
    (d : database.DateTime) (hd : 0 ≤ d.val) (hge : nanos t ≤ d.val * 1000000)
    (hnone : ∀ a b, dnanos a = d.val * 1000000 → dnanos b = nanos t →
      durationCheckedSub a b = ok none) :
    dateTimeTryInto d = ok (.Err .TimeArithmetic)

end DateTime

section DateTimeError
open database.DateTimeError.Insts
open core.num.error
open CoreConvertFromSystemTimeError renaming «from» → dateTimeErrorFromSystemTime
open CoreConvertFromTryFromIntError renaming «from» → dateTimeErrorFromTryFromInt

recall date_time_error_from_system_time_error (e : std.time.SystemTimeError) :
    dateTimeErrorFromSystemTime e = ok (.SystemTimeError e)

recall date_time_error_from_try_from_int_error (e : TryFromIntError) :
    dateTimeErrorFromTryFromInt e = ok (.TypeConversion e)

end DateTimeError

section KeyLifeCycle
open database.KeyLifeCycle.Insts
open CoreCloneClone renaming clone → keyLifeCycleClone
open CoreCmpPartialEqKeyLifeCycle renaming eq → keyLifeCycleEq
open CoreCmpOrd renaming cmp → keyLifeCycleCmp
open CoreCmpPartialOrdKeyLifeCycle renaming partial_cmp → keyLifeCyclePartialCmp

recall key_life_cycle_clone (x : database.KeyLifeCycle) : keyLifeCycleClone x = ok x

recall key_life_cycle_eq (a b : database.KeyLifeCycle) :
    ∃ r, keyLifeCycleEq a b = ok r ∧ (r = true ↔ a = b)

recall key_life_cycle_cmp (a b : database.KeyLifeCycle) :
    keyLifeCycleCmp a b = ok (compare (keyLifeCycleRank a) (keyLifeCycleRank b))

recall key_life_cycle_partial_cmp (a b : database.KeyLifeCycle) :
    keyLifeCyclePartialCmp a b =
      ok (some (compare (keyLifeCycleRank a) (keyLifeCycleRank b)))

end KeyLifeCycle

section BlobState
open database.BlobState.Insts
open CoreCloneClone renaming clone → blobStateClone
open CoreCmpPartialEqBlobState renaming eq → blobStateEq
open CoreCmpOrd renaming cmp → blobStateCmp
open CoreCmpPartialOrdBlobState renaming partial_cmp → blobStatePartialCmp
open CoreDefaultDefault renaming default → blobStateDefault

recall blob_state_clone (x : database.BlobState) : blobStateClone x = ok x

recall blob_state_default : blobStateDefault = ok database.BlobState.Current

recall blob_state_eq (a b : database.BlobState) :
    ∃ r, blobStateEq a b = ok r ∧ (r = true ↔ a = b)

recall blob_state_cmp (a b : database.BlobState) :
    blobStateCmp a b = ok (compare (blobStateRank a) (blobStateRank b))

recall blob_state_partial_cmp (a b : database.BlobState) :
    blobStatePartialCmp a b = ok (some (compare (blobStateRank a) (blobStateRank b)))

end BlobState

section KeyEntryLoadBits
open database.KeyEntryLoadBits.Insts
open CoreCloneClone renaming clone → loadBitsClone
open CoreCmpPartialEqKeyEntryLoadBits renaming eq → loadBitsEq
open CoreCmpOrd renaming cmp → loadBitsCmp
open CoreCmpPartialOrdKeyEntryLoadBits renaming partial_cmp → loadBitsPartialCmp
open database.KeyEntryLoadBits renaming load_public → loadBitsPublic
open database.KeyEntryLoadBits renaming load_km → loadBitsKm

recall key_entry_load_bits_clone (x : database.KeyEntryLoadBits) :
    loadBitsClone x = ok x

recall key_entry_load_bits_eq (a b : database.KeyEntryLoadBits) :
    ∃ r, loadBitsEq a b = ok r ∧ (r = true ↔ a = b)

recall key_entry_load_bits_cmp (a b : database.KeyEntryLoadBits) :
    loadBitsCmp a b = ok (compare a.val b.val)

recall key_entry_load_bits_partial_cmp (a b : database.KeyEntryLoadBits) :
    loadBitsPartialCmp a b = ok (some (compare a.val b.val))

recall key_entry_load_bits_load_public (x : database.KeyEntryLoadBits) :
    ∃ b, loadBitsPublic x = ok b ∧ (b = true ↔ (x &&& 2#u32) ≠ 0#u32)

recall key_entry_load_bits_load_km (x : database.KeyEntryLoadBits) :
    ∃ b, loadBitsKm x = ok b ∧ (b = true ↔ (x &&& 1#u32) ≠ 0#u32)

recall key_entry_load_bits_constants :
    loadBitsPublic database.KeyEntryLoadBits.NONE = ok false ∧
    loadBitsKm database.KeyEntryLoadBits.NONE = ok false ∧
    loadBitsPublic database.KeyEntryLoadBits.KM = ok false ∧
    loadBitsKm database.KeyEntryLoadBits.KM = ok true ∧
    loadBitsPublic database.KeyEntryLoadBits.PUBLIC = ok true ∧
    loadBitsKm database.KeyEntryLoadBits.PUBLIC = ok false ∧
    loadBitsPublic database.KeyEntryLoadBits.BOTH = ok true ∧
    loadBitsKm database.KeyEntryLoadBits.BOTH = ok true

end KeyEntryLoadBits

section KeyIdGuard
open std.sync.poison
open database.KeyIdGuard renaming id → keyIdGuardId
open database.KeyIdLockDb renaming try_get → keyIdLockDbTryGet

recall key_id_guard_id (g : database.KeyIdGuard) : keyIdGuardId g = ok g

recall key_id_lock_db_try_get_acquired (self : database.KeyIdLockDb) (key_id : Std.I64)
    (g : KeySetGuard) (hs hs' : KeySet) (back : KeySet → KeySetGuard)
    (hlock : keySetLock self.locked_keys = ok (.Ok g))
    (hderef : keySetDerefMut g = ok (hs, back))
    (hins : keySetInsert hs key_id = ok (true, hs')) :
    keyIdLockDbTryGet self key_id = ok (some key_id)

recall key_id_lock_db_try_get_taken (self : database.KeyIdLockDb) (key_id : Std.I64)
    (g : KeySetGuard) (hs hs' : KeySet) (back : KeySet → KeySetGuard)
    (hlock : keySetLock self.locked_keys = ok (.Ok g))
    (hderef : keySetDerefMut g = ok (hs, back))
    (hins : keySetInsert hs key_id = ok (false, hs')) :
    keyIdLockDbTryGet self key_id = ok none

recall key_id_lock_db_try_get_poisoned (self : database.KeyIdLockDb) (key_id : Std.I64)
    (e : PoisonError KeySetGuard)
    (hlock : keySetLock self.locked_keys = ok (.Err e)) :
    keyIdLockDbTryGet self key_id = fail .panic

end KeyIdGuard

section CertificateInfo
open database.CertificateInfo.Insts.CoreDefaultDefault renaming default → certInfoDefault
open database.CertificateInfo renaming take_cert → certInfoTakeCert
open database.CertificateInfo renaming take_cert_chain → certInfoTakeCertChain
open database.BlobInfo renaming new_with_superseded → blobInfoNewWithSuperseded

recall certificate_info_default (h : OptionDefaultSpec (alloc.vec.Vec Std.U8)) :
    certInfoDefault = ok { cert := none, cert_chain := none }

recall certificate_info_take_cert (c : database.CertificateInfo) :
    certInfoTakeCert c = ok (c.cert, { c with cert := none })

recall certificate_info_take_cert_chain (c : database.CertificateInfo) :
    certInfoTakeCertChain c = ok (c.cert_chain, { c with cert_chain := none })

recall blob_info_new_with_superseded (blob : Slice Std.U8) (md : database.BlobMetaData)
    (sup : Option (Slice Std.U8 × database.BlobMetaData)) :
    blobInfoNewWithSuperseded blob md sup =
      ok { blob := blob, metadata := md, superseded_blob := sup }

end CertificateInfo

section KeyEntry
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

recall key_entry_default (view : MetaView database.KeyMetaEntry)
    (hblob : OptionDefaultSpec (alloc.vec.Vec Std.U8 × database.BlobMetaData))
    (hcert : OptionDefaultSpec (alloc.vec.Vec Std.U8))
    (hparams : VecDefaultSpec key_parameter.KeyParameter)
    (hmap : HashMapDefaultSpec database.KeyMetaEntry view) :
    ∃ e, keyEntryDefault = ok e ∧ e.id.val = 0 ∧ e.key_blob_info = none ∧ e.cert = none ∧
      e.cert_chain = none ∧ e.km_uuid.val = List.replicate 16 (0#u8) ∧ e.parameters.val = [] ∧
      (∀ k, view e.metadata.data k = none) ∧ e.pure_cert = false

recall key_entry_eq_id_pure (a b : database.KeyEntry) :
    (a.id ≠ b.id → keyEntryEq a b = ok false) ∧
    (a.id = b.id → a.pure_cert ≠ b.pure_cert → keyEntryEq a b = ok false)

recall key_entry_eq_blob (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert) :
    (∀ f, blobInfoEq a.key_blob_info b.key_blob_info = fail f → keyEntryEq a b = fail f) ∧
    (blobInfoEq a.key_blob_info b.key_blob_info = ok false → keyEntryEq a b = ok false)

recall key_entry_eq_blob_absent (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hopt : OptionEqSpec (Pair.Insts.CoreCmpPartialEqPair
      (core.cmp.PartialEqVec core.cmp.PartialEqU8) blobMetaDataEq)) :
    (a.key_blob_info.isSome ≠ b.key_blob_info.isSome → keyEntryEq a b = ok false) ∧
    (a.key_blob_info = none → b.key_blob_info = none →
      blobInfoEq a.key_blob_info b.key_blob_info = ok true)

recall key_entry_eq_certs (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hkb : blobInfoEq a.key_blob_info b.key_blob_info = ok true)
    (hopt : OptionEqSpec (core.cmp.PartialEqVec core.cmp.PartialEqU8)) :
    (a.cert ≠ b.cert → keyEntryEq a b = ok false) ∧
    (a.cert = b.cert → a.cert_chain ≠ b.cert_chain → keyEntryEq a b = ok false) ∧
    (a.cert = b.cert → a.cert_chain = b.cert_chain → a.km_uuid ≠ b.km_uuid →
      keyEntryEq a b = ok false)

recall key_entry_eq_parameters (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hkb : blobInfoEq a.key_blob_info b.key_blob_info = ok true)
    (hopt : OptionEqSpec (core.cmp.PartialEqVec core.cmp.PartialEqU8))
    (hcert : a.cert = b.cert) (hchain : a.cert_chain = b.cert_chain)
    (huuid : a.km_uuid = b.km_uuid) :
    (∀ f, keyParametersEq a.parameters b.parameters = fail f → keyEntryEq a b = fail f) ∧
    (keyParametersEq a.parameters b.parameters = ok false → keyEntryEq a b = ok false)

recall key_entry_eq_metadata (a b : database.KeyEntry) (hid : a.id = b.id)
    (hpure : a.pure_cert = b.pure_cert)
    (hkb : blobInfoEq a.key_blob_info b.key_blob_info = ok true)
    (hopt : OptionEqSpec (core.cmp.PartialEqVec core.cmp.PartialEqU8))
    (hcert : a.cert = b.cert) (hchain : a.cert_chain = b.cert_chain)
    (huuid : a.km_uuid = b.km_uuid)
    (hp : keyParametersEq a.parameters b.parameters = ok true) :
    (∀ f, keyMetaDataEq a.metadata b.metadata = fail f → keyEntryEq a b = fail f) ∧
    (∀ m, keyMetaDataEq a.metadata b.metadata = ok m → keyEntryEq a b = ok m)

recall key_entry_id (e : database.KeyEntry) : keyEntryId e = ok e.id

recall key_entry_key_blob_info (e : database.KeyEntry) :
    keyEntryKeyBlobInfo e = ok e.key_blob_info

recall key_entry_take_key_blob_info (e : database.KeyEntry) :
    keyEntryTakeKeyBlobInfo e = ok (e.key_blob_info, { e with key_blob_info := none })

recall key_entry_cert (e : database.KeyEntry) : keyEntryCert e = ok e.cert

recall key_entry_take_cert (e : database.KeyEntry) :
    keyEntryTakeCert e = ok (e.cert, { e with cert := none })

recall key_entry_take_cert_chain (e : database.KeyEntry) :
    keyEntryTakeCertChain e = ok (e.cert_chain, { e with cert_chain := none })

recall key_entry_km_uuid (e : database.KeyEntry) : keyEntryKmUuid e = ok e.km_uuid

recall key_entry_into_key_parameters (e : database.KeyEntry) :
    keyEntryIntoKeyParameters e = ok e.parameters

recall key_entry_metadata (e : database.KeyEntry) : keyEntryMetadata e = ok e.metadata

recall key_entry_pure_cert (e : database.KeyEntry) : keyEntryPureCert e = ok e.pure_cert

recall key_entry_is_attested (e : database.KeyEntry) :
    keyEntryIsAttested e = ok e.cert_chain.isSome

end KeyEntry

section SubComponentType
open database.SubComponentType.Insts
open CoreCloneClone renaming clone → subComponentTypeClone
open CoreCmpPartialEqSubComponentType renaming eq → subComponentTypeEq
open CoreCmpOrd renaming cmp → subComponentTypeCmp
open CoreCmpPartialOrdSubComponentType renaming partial_cmp → subComponentTypePartialCmp

recall sub_component_type_clone (x : database.SubComponentType) :
    subComponentTypeClone x = ok x

recall sub_component_type_eq (a b : database.SubComponentType) :
    ∃ r, subComponentTypeEq a b = ok r ∧ (r = true ↔ a = b)

recall sub_component_type_cmp (a b : database.SubComponentType) :
    subComponentTypeCmp a b = ok (compare a.val b.val)

recall sub_component_type_partial_cmp (a b : database.SubComponentType) :
    subComponentTypePartialCmp a b = ok (some (compare a.val b.val))

end SubComponentType

section DoGc
open core.result.ResultTError.Insts.Keystore2DatabaseDoGc renaming do_gc → doGc
open core.result.ResultTError.Insts.Keystore2DatabaseDoGc renaming no_gc → noGc
open core.result.ResultTError.Insts.Keystore2DatabaseDoGc renaming need_gc → needGc

recall do_gc_result {T : Type} (root : anyhow.Error → ErrRoot) :
    (∀ (v : T) (b : Bool),
      doGc (.Ok v : core.result.Result T anyhow.Error) b = ok (.Ok (b, v))) ∧
    (∀ (e : anyhow.Error) (b : Bool), ∃ e',
      doGc (.Err e : core.result.Result T anyhow.Error) b = ok (.Err e') ∧ root e' = root e)

recall no_gc_result {T : Type} (root : anyhow.Error → ErrRoot) :
    (∀ v : T, noGc (.Ok v : core.result.Result T anyhow.Error) = ok (.Ok (false, v))) ∧
    (∀ e : anyhow.Error, ∃ e',
      noGc (.Err e : core.result.Result T anyhow.Error) = ok (.Err e') ∧ root e' = root e)

recall need_gc_result {T : Type} (root : anyhow.Error → ErrRoot) :
    (∀ v : T, needGc (.Ok v : core.result.Result T anyhow.Error) = ok (.Ok (true, v))) ∧
    (∀ e : anyhow.Error, ∃ e',
      needGc (.Err e : core.result.Result T anyhow.Error) = ok (.Err e') ∧ root e' = root e)

end DoGc

section BootTime
open database.BootTime.Insts
open CoreCloneClone renaming clone → bootTimeClone
open CoreCmpPartialEqBootTime renaming eq → bootTimeEq
open CoreCmpOrd renaming cmp → bootTimeCmp
open CoreCmpPartialOrdBootTime renaming partial_cmp → bootTimePartialCmp
open CoreDefaultDefault renaming default → bootTimeDefault
open database.BootTime renaming now → bootTimeNow
open database.BootTime renaming milliseconds → bootTimeMilliseconds
open database.BootTime renaming seconds → bootTimeSeconds
open database.BootTime renaming checked_sub → bootTimeCheckedSub

recall boot_time_clone (x : database.BootTime) : bootTimeClone x = ok x

recall boot_time_default : bootTimeDefault = ok 0#i64

recall boot_time_eq (a b : database.BootTime) :
    ∃ r, bootTimeEq a b = ok r ∧ (r = true ↔ a = b)

recall boot_time_cmp (a b : database.BootTime) :
    bootTimeCmp a b = ok (compare a.val b.val)

recall boot_time_partial_cmp (a b : database.BootTime) :
    bootTimePartialCmp a b = ok (some (compare a.val b.val))

recall boot_time_now (t : Std.I64) (h : utils.get_current_time_in_milliseconds = ok t) :
    bootTimeNow = ok t

recall boot_time_milliseconds (x : database.BootTime) : bootTimeMilliseconds x = ok x

recall boot_time_seconds (x : database.BootTime) :
    ∃ r, bootTimeSeconds x = ok r ∧ r.val = Int.tdiv x.val 1000

recall boot_time_checked_sub_some (a b : database.BootTime)
    (h : Std.I64.min ≤ a.val - b.val ∧ a.val - b.val ≤ Std.I64.max) :
    ∃ r, bootTimeCheckedSub a b = ok (some r) ∧ r.val = a.val - b.val

recall boot_time_checked_sub_none (a b : database.BootTime)
    (h : a.val - b.val < Std.I64.min ∨ Std.I64.max < a.val - b.val) :
    bootTimeCheckedSub a b = ok none

end BootTime

section AuthTokenEntry
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open database.AuthTokenEntry.Insts.CoreCloneClone renaming clone → authTokenEntryClone
open database.AuthTokenEntry.satisfies.closure.Insts
  renaming CoreOpsFunctionFnMutTupleShared0SecureUserIdBool → satisfiesFnMut
open database.AuthTokenEntry renaming satisfies → authTokenEntrySatisfies
open database.AuthTokenEntry.impl renaming auth_token → authTokenEntryAuthToken
open database.AuthTokenEntry renaming take_auth_token → authTokenEntryTakeAuthToken
open database.AuthTokenEntry.impl renaming time_received → authTokenEntryTimeReceived
open database.AuthTokenEntry renaming challenge → authTokenEntryChallenge

recall auth_token_entry_clone (h : HardwareAuthTokenCloneSpec)
    (e : database.AuthTokenEntry) : authTokenEntryClone e = ok e

recall auth_token_entry_satisfies
    (h : IterAnySpec satisfiesFnMut)
    (e : database.AuthTokenEntry) (sids : Slice utils.SecureUserId)
    (t : HardwareAuthenticatorType.HardwareAuthenticatorType) :
    ∃ b, authTokenEntrySatisfies e sids t = ok b ∧
      (b = true ↔ ∃ sid ∈ sids.val,
        (sid = e.auth_token.userId ∨ sid = e.auth_token.authenticatorId) ∧
        (t &&& e.auth_token.authenticatorType) ≠ 0#i32)

recall auth_token_entry_auth_token (e : database.AuthTokenEntry) :
    authTokenEntryAuthToken e = ok e.auth_token

recall auth_token_entry_take_auth_token (e : database.AuthTokenEntry) :
    authTokenEntryTakeAuthToken e = ok e.auth_token

recall auth_token_entry_time_received (e : database.AuthTokenEntry) :
    authTokenEntryTimeReceived e = ok e.time_received

recall auth_token_entry_challenge (e : database.AuthTokenEntry) :
    authTokenEntryChallenge e = ok e.auth_token.challenge

end AuthTokenEntry

end Keystore2Verify.Database
