import Keystore2Verify.Proofs.DatabaseKeystoreDb.MakePersistentPath
import Keystore2Verify.Proofs.DatabaseKeystoreDb.GetTotalSize
import Keystore2Verify.Proofs.DatabaseKeystoreDb.GetTableSize
import Keystore2Verify.Proofs.DatabaseKeystoreDb.GetStorageStat
import Keystore2Verify.Proofs.DatabaseKeystoreDb.SetDeletedBlob
import Keystore2Verify.Proofs.DatabaseKeystoreDb.StoreNewKey
import Keystore2Verify.Proofs.DatabaseKeystoreDb.StoreNewCertificate
import Keystore2Verify.Proofs.DatabaseKeystoreDb.LoadKeyEntry
import Keystore2Verify.Proofs.DatabaseKeystoreDb.DeleteReceivedGrants
import Keystore2Verify.Proofs.DatabaseKeystoreDb.UnbindKey
import Keystore2Verify.Proofs.DatabaseKeystoreDb.GetKeyKmUuid
import Keystore2Verify.Proofs.DatabaseKeystoreDb.LoadKeyComponents
import Keystore2Verify.Proofs.DatabaseKeystoreDb.InsertAuthToken
import Keystore2Verify.Proofs.DatabaseKeystoreDb.FindAuthTokenEntry
import Keystore2Verify.Proofs.DatabaseKeystoreDb.LoadKeyDescriptor
import Keystore2Verify.Proofs.DatabaseKeystoreDb.Pragma

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section MakePersistentPath

recall make_persistent_path_ok (db_root : std.path.Path) (u : String)
    (h : u.toByteArray.size ≤ U32.max)
    (hto : StrToOwnedSpec) (hpush : StringPushStrSpec)
    (hpath : persistentPathLossy db_root = ok (toStr u h)) :
    database.KeystoreDB.make_persistent_path db_root = ok (.Ok ("file:" ++ u))

end MakePersistentPath

section GetTotalSize
open android_security_metrics.aidl.android.security.metrics

recall get_total_size_query (self : database.KeystoreDB) (s : Storage.Storage)
    (hdb : Storage.Storage.DATABASE = ok s) :
    database.KeystoreDB.get_total_size self =
      database.KeystoreDB.do_table_size_query self s (toStr
        ("SELECT page_count * page_size, freelist_count * page_size\n" ++
         "             FROM pragma_page_count(\'persistent\'),\n" ++
         "                  pragma_page_size(\'persistent\'),\n" ++
         "                  persistent.pragma_freelist_count();"))
        (Array.to_slice (Std.Array.empty Str))

end GetTotalSize

section GetTableSize
open android_security_metrics.aidl.android.security.metrics

recall get_table_size_query (self : database.KeystoreDB) (storage_type : Storage.Storage)
    (schema table : Str) :
    database.KeystoreDB.get_table_size self storage_type schema table =
      database.KeystoreDB.do_table_size_query self storage_type (toStr
        "SELECT pgsize,unused FROM dbstat(?1)\n             WHERE name=?2 AND aggregate=TRUE;")
        (Array.to_slice (Array.make 2#usize [ schema, table ]))

end GetTableSize

section GetStorageStat
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open database.perboot.PerbootDB renaming auth_tokens_len → authTokensLen
open android_security_metrics.aidl.android.security.metrics

recall get_storage_stat_database (self : database.KeystoreDB) (st : Storage.Storage)
    (h : st.val = storageDatabase) :
    database.KeystoreDB.get_storage_stat self st = database.KeystoreDB.get_total_size self

recall get_storage_stat_table (self : database.KeystoreDB) (st : Storage.Storage) (t : Str)
    (h : storageTableName st.val = some t) :
    database.KeystoreDB.get_storage_stat self st =
      database.KeystoreDB.get_table_size self st (toStr "persistent") t

recall get_storage_stat_auth_token (self : database.KeystoreDB) (st : Storage.Storage)
    (pd : database.perboot.PerbootDB) (n sz : Std.Usize)
    (h : st.val = storageAuthToken)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hlen : authTokensLen pd = ok n)
    (hsz : core.mem.size_of database.AuthTokenEntry = ok sz)
    (hfit : n.val * sz.val ≤ Std.Usize.max) :
    ∃ stats : StorageStats.StorageStats,
      database.KeystoreDB.get_storage_stat self st = ok (.Ok stats, self) ∧
      stats.storage_type = st ∧ stats.unused_size = 0#i32 ∧
      stats.size.bv = BitVec.ofNat 32 (n.val * sz.val)

recall get_storage_stat_auth_token_overflow (self : database.KeystoreDB) (st : Storage.Storage)
    (pd : database.perboot.PerbootDB) (n sz : Std.Usize)
    (h : st.val = storageAuthToken)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hlen : authTokensLen pd = ok n)
    (hsz : core.mem.size_of database.AuthTokenEntry = ok sz)
    (hover : Std.Usize.max < n.val * sz.val) :
    database.KeystoreDB.get_storage_stat self st = fail Error.integerOverflow

recall get_storage_stat_auth_token_len_failure (self : database.KeystoreDB)
    (st : Storage.Storage) (pd : database.perboot.PerbootDB) (err : Error)
    (h : st.val = storageAuthToken)
    (hderef : arcDeref alloc.alloc.Global self.perboot = ok pd)
    (hlen : authTokensLen pd = fail err) :
    database.KeystoreDB.get_storage_stat self st = fail err

recall get_storage_stat_unsupported (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (st : Storage.Storage)
    (hdb : st.val ≠ storageDatabase) (hauth : st.val ≠ storageAuthToken)
    (htab : storageTableName st.val = none)
    (hfmt : AllocFmtFormatSpec) (hmsg : AnyhowErrorMsgSpec root) :
    ∃ e, database.KeystoreDB.get_storage_stat self st = ok (.Err e, self) ∧
      root e = ErrRoot.other

end GetStorageStat

section SetDeletedBlob
open database.KeystoreDB.set_deleted_blob.closure.Insts renaming
  CoreOpsFunctionFnTupleShared2TransactionResultPairBoolTupleError → deletedBlobFn

recall set_deleted_blob_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (blob : Slice Std.U8) (blob_metadata : database.BlobMetaData)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result Unit anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::set_deleted_blob") = ok w)
    (hwt : database.KeystoreDB.with_transaction deletedBlobFn self
      (database.TransactionBehavior.Immediate (toStr "TX_set_deleted_blob"))
      (blob, blob_metadata) = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root Unit) :
    ∃ r1, database.KeystoreDB.set_deleted_blob self blob blob_metadata = ok (r1, self1) ∧
      ContextOutcome root r r1

end SetDeletedBlob

section StoreNewKey
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.store_new_key.closure.Insts renaming
  CoreOpsFunctionFnTupleShared10TransactionResultPairBoolKeyIdGuardError → newKeyFn
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
  renaming INVALID_ARGUMENT → invalidArgument

recall store_new_key_no_alias (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = none)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument)

recall store_new_key_bad_domain (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = some a) (h0 : key.domain ≠ 0#i32) (h2 : key.domain ≠ 2#i32)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument)

recall store_new_key_has_blob (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid) (a : String)
    (b : alloc.vec.Vec Std.U8) (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = some b)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument)

recall store_new_key_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (params : Slice key_parameter.KeyParameter)
    (blob_info : database.BlobInfo) (cert_info : database.CertificateInfo)
    (metadata : database.KeyMetaData) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result database.KeyIdGuard anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_key") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = none)
    (hwt : database.KeystoreDB.with_transaction newKeyFn self
      (database.TransactionBehavior.Immediate (toStr "TX_store_new_key"))
      (key.domain, key.nspace, key_type, km_uuid, blob_info, cert_info, params, metadata, a) =
        ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root database.KeyIdGuard) :
    ∃ r1, database.KeystoreDB.store_new_key self key key_type params blob_info cert_info metadata
        km_uuid = ok (r1, self1) ∧ ContextOutcome root r r1

end StoreNewKey

section StoreNewCertificate
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.store_new_certificate.closure.Insts renaming
  CoreOpsFunctionFnTupleShared6TransactionResultPairBoolKeyIdGuardError → newCertFn
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode.ResponseCode
  renaming INVALID_ARGUMENT → invalidArgument

recall store_new_certificate_no_alias (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = none)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument)

recall store_new_certificate_bad_domain (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = some a) (h0 : key.domain ≠ 0#i32) (h2 : key.domain ≠ 2#i32)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument)

recall store_new_certificate_has_blob (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid) (a : String)
    (b : alloc.vec.Vec Std.U8) (w : Option watchdog_helper.watchdog.WatchPoint)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = some b)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : KsErrCtxLaw root database.KeyIdGuard) :
    ∃ e, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (.Err e, self) ∧ root e = ErrRoot.ks (error.Error.Rc invalidArgument)

recall store_new_certificate_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (cert : Slice Std.U8) (km_uuid : database.Uuid) (a : String)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result database.KeyIdGuard anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::store_new_certificate") = ok w)
    (halias : key.alias = some a) (hdom : key.domain = 0#i32 ∨ key.domain = 2#i32)
    (hblob : key.blob = none)
    (hwt : database.KeystoreDB.with_transaction newCertFn self
      (database.TransactionBehavior.Immediate (toStr "TX_store_new_certificate"))
      (key.domain, key.nspace, key_type, km_uuid, cert, a) = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root database.KeyIdGuard) :
    ∃ r1, database.KeystoreDB.store_new_certificate self key key_type cert km_uuid =
        ok (r1, self1) ∧ ContextOutcome root r r1

end StoreNewCertificate

section LoadKeyEntry
open core.ops.function renaming Fn → FnTrait
open std.thread.functions renaming sleep → threadSleep
open Keystore2Verify.Permission (KeyDesc)

recall load_key_entry_success {T0 : Type _}
    (inst : FnTrait T0
      (KeyDesc × Option permission.KeyPermSet)
      (core.result.Result Unit anyhow.Error))
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (load_bits : database.KeyEntryLoadBits)
    (caller_uid : utils.AppUid) (check_permission : T0)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (x : database.KeyIdGuard × database.KeyEntry)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::load_key_entry") = ok w)
    (hint : database.KeystoreDB.load_key_entry_internal inst self key key_type load_bits
      caller_uid check_permission = ok (.Ok x, self1)) :
    database.KeystoreDB.load_key_entry inst self key key_type load_bits caller_uid
      check_permission = ok (.Ok x, self1)

recall load_key_entry_other_error (root : anyhow.Error → ErrRoot) {T0 : Type _}
    (inst : FnTrait T0
      (KeyDesc × Option permission.KeyPermSet)
      (core.result.Result Unit anyhow.Error))
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (load_bits : database.KeyEntryLoadBits)
    (caller_uid : utils.AppUid) (check_permission : T0)
    (w : Option watchdog_helper.watchdog.WatchPoint) (e : anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::load_key_entry") = ok w)
    (hint : database.KeystoreDB.load_key_entry_internal inst self key key_type load_bits
      caller_uid check_permission = ok (.Err e, self1))
    (hlock : database.KeystoreDB.is_locked_error e = ok false)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry)) :
    ∃ e', database.KeystoreDB.load_key_entry inst self key key_type load_bits caller_uid
        check_permission = ok (.Err e', self1) ∧ root e' = root e

recall load_key_entry_locked_retry {T0 : Type _}
    (inst : FnTrait T0
      (KeyDesc × Option permission.KeyPermSet)
      (core.result.Result Unit anyhow.Error))
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (load_bits : database.KeyEntryLoadBits)
    (caller_uid : utils.AppUid) (check_permission : T0)
    (w : Option watchdog_helper.watchdog.WatchPoint) (e : anyhow.Error)
    (d : core.time.Duration)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::load_key_entry") = ok w)
    (hint : database.KeystoreDB.load_key_entry_internal inst self key key_type load_bits
      caller_uid check_permission = ok (.Err e, self1))
    (hlock : database.KeystoreDB.is_locked_error e = ok true)
    (hd : database.DB_BUSY_RETRY_INTERVAL = ok d)
    (hsleep : threadSleep d = ok ()) :
    database.KeystoreDB.load_key_entry inst self key key_type load_bits caller_uid
      check_permission =
    database.KeystoreDB.load_key_entry_loop inst check_permission self1 key key_type load_bits
      caller_uid

end LoadKeyEntry

section DeleteReceivedGrants
open alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open rusqlite.transaction.Transaction.Insts.CoreOpsDerefDerefConnection renaming deref → txDeref
open I32.Insts renaming RusqliteTypesTo_sqlToSql → i32ToSql

recall delete_received_grants_deleted (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (user : utils.AndroidUserId)
    (c : rusqlite.Connection) (off : Std.U32) (n : Std.Usize)
    (hderef : txDeref tx = ok c)
    (hoff : utils.AID_USER_OFFSET = ok off)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hexec : rusqlite.Connection.execute
      Shared0SliceShared1P.Insts.RusqliteParamsParams c sv
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i32ToSql user ])) = ok (.Ok n))
    (hctx : RusqliteCtxLaw rootSql root Std.Usize) :
    ∃ b, database.KeystoreDB.delete_received_grants tx user = ok (.Ok b) ∧
      (b = true ↔ n.val ≠ 0)

recall delete_received_grants_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (user : utils.AndroidUserId)
    (c : rusqlite.Connection) (off : Std.U32) (x : rusqlite.error.Error)
    (hderef : txDeref tx = ok c)
    (hoff : utils.AID_USER_OFFSET = ok off)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hexec : rusqlite.Connection.execute
      Shared0SliceShared1P.Insts.RusqliteParamsParams c sv
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i32ToSql user ])) = ok (.Err x))
    (hctx : RusqliteCtxLaw rootSql root Std.Usize) :
    ∃ e, database.KeystoreDB.delete_received_grants tx user = ok (.Err e) ∧
      root e = rootSql x

end DeleteReceivedGrants

section UnbindKey
open core.ops.function renaming Fn → FnTrait
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.unbind_key.closure.Insts renaming
  CoreOpsFunctionFnTupleShared4TransactionResultPairBoolTupleError → unbindFn

recall unbind_key_transaction (root : anyhow.Error → ErrRoot) {T0 : Type _}
    (inst : FnTrait T0
      (KeyDesc × Option permission.KeyPermSet)
      (core.result.Result Unit anyhow.Error))
    (self self1 : database.KeystoreDB) (key : KeyDesc)
    (key_type : database.KeyType) (caller_uid : utils.AppUid) (check_permission : T0)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result Unit anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::unbind_key") = ok w)
    (hwt : database.KeystoreDB.with_transaction (unbindFn inst) self
      (database.TransactionBehavior.Immediate (toStr "TX_unbind_key"))
      (key, key_type, caller_uid, check_permission) = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root Unit) :
    ∃ r1, database.KeystoreDB.unbind_key inst self key key_type caller_uid check_permission =
        ok (r1, self1) ∧ ContextOutcome root r r1

end UnbindKey

section GetKeyKmUuid
open rusqlite.transaction.Transaction.Insts.CoreOpsDerefDerefConnection renaming deref → txDeref
open I64.Insts renaming RusqliteTypesTo_sqlToSql → i64ToSql
open database.KeystoreDB.get_key_km_uuid.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0RowResultUuidError → kmUuidRow

recall get_key_km_uuid_found (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (key_id : Std.I64) (c : rusqlite.Connection)
    (u : database.Uuid)
    (hderef : txDeref tx = ok c)
    (hquery : rusqlite.Connection.query_row Shared0SliceShared1P.Insts.RusqliteParamsParams
      kmUuidRow c (toStr "SELECT km_uuid FROM persistent.keyentry WHERE id = ?")
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i64ToSql key_id ])) () = ok (.Ok u))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : RusqliteCtxLaw rootSql root database.Uuid) :
    database.KeystoreDB.get_key_km_uuid tx key_id = ok (.Ok u)

recall get_key_km_uuid_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction) (key_id : Std.I64) (c : rusqlite.Connection)
    (x : rusqlite.error.Error)
    (hderef : txDeref tx = ok c)
    (hquery : rusqlite.Connection.query_row Shared0SliceShared1P.Insts.RusqliteParamsParams
      kmUuidRow c (toStr "SELECT km_uuid FROM persistent.keyentry WHERE id = ?")
      (Array.to_slice (Array.make 1#usize [ Dyn.mk _ i64ToSql key_id ])) () = ok (.Err x))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : RusqliteCtxLaw rootSql root database.Uuid) :
    ∃ e, database.KeystoreDB.get_key_km_uuid tx key_id = ok (.Err e) ∧
      root e = rootSql x

end GetKeyKmUuid

section LoadKeyComponents
open Keystore2Verify.Permission (AnyhowStrCtxLaw)

recall load_key_components_ok (root : anyhow.Error → ErrRoot)
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
                km_uuid := u, parameters := ps, metadata := m, pure_cert := (¬ has) })

recall load_key_components_metadata_error (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (x : anyhow.Error)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Err x))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData) :
    ∃ e, database.KeystoreDB.load_key_components tx load_bits key_id = ok (.Err e) ∧
      root e = root x

recall load_key_components_blob_error (root : anyhow.Error → ErrRoot)
    (tx : rusqlite.transaction.Transaction)
    (load_bits : database.KeyEntryLoadBits) (key_id : Std.I64)
    (m : database.KeyMetaData) (x : anyhow.Error)
    (hm : database.KeyMetaData.load_from_db key_id tx = ok (.Ok m))
    (hb : database.KeystoreDB.load_blob_components key_id load_bits tx = ok (.Err x))
    (h1 : AnyhowStrCtxLaw root database.KeyMetaData)
    (h2 : AnyhowStrCtxLaw root BlobComponents) :
    ∃ e, database.KeystoreDB.load_key_components tx load_bits key_id = ok (.Err e) ∧
      root e = root x

recall load_key_components_parameters_error (root : anyhow.Error → ErrRoot)
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
      root e = root x

recall load_key_components_uuid_error (root : anyhow.Error → ErrRoot)
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
      root e = root x

end LoadKeyComponents

section InsertAuthToken
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open database.perboot.PerbootDB renaming insert_auth_token_entry → insertAuthTokenEntry
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone renaming clone → hatClone

recall insert_auth_token_ok (self : database.KeystoreDB)
    (auth_token : HardwareAuthToken.HardwareAuthToken)
    (pd : database.perboot.PerbootDB) (hat : HardwareAuthToken.HardwareAuthToken)
    (bt : database.BootTime) (ate : database.AuthTokenEntry)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hclone : hatClone auth_token = ok hat)
    (hnow : database.BootTime.now = ok bt)
    (hnew : database.AuthTokenEntry.new hat bt = ok ate)
    (hins : insertAuthTokenEntry pd ate = ok ()) :
    database.KeystoreDB.insert_auth_token self auth_token = ok self

recall insert_auth_token_failure (self : database.KeystoreDB)
    (auth_token : HardwareAuthToken.HardwareAuthToken)
    (pd : database.perboot.PerbootDB) (hat : HardwareAuthToken.HardwareAuthToken)
    (bt : database.BootTime) (ate : database.AuthTokenEntry) (err : Error)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hclone : hatClone auth_token = ok hat)
    (hnow : database.BootTime.now = ok bt)
    (hnew : database.AuthTokenEntry.new hat bt = ok ate)
    (hins : insertAuthTokenEntry pd ate = fail err) :
    database.KeystoreDB.insert_auth_token self auth_token = fail err

end InsertAuthToken

section FindAuthTokenEntry
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open database.perboot.PerbootDB renaming find_auth_token_entry → findAuthTokenEntry
open core.ops.function renaming Fn → FnTrait

recall find_auth_token_entry_search {F : Type _}
    (inst : FnTrait F database.AuthTokenEntry Bool)
    (self : database.KeystoreDB) (p : F) (pd : database.perboot.PerbootDB)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd) :
    database.KeystoreDB.find_auth_token_entry inst self p =
      findAuthTokenEntry inst pd p

end FindAuthTokenEntry

section LoadKeyDescriptor
open Keystore2Verify.Permission (KeyDesc)
open database.KeystoreDB.load_key_descriptor.closure.Insts renaming
  CoreOpsFunctionFnTupleShared1TransactionResultPairBoolOptionKeyDescriptorError → descriptorFn

recall load_key_descriptor_transaction (root : anyhow.Error → ErrRoot)
    (self self1 : database.KeystoreDB) (key_id : Std.I64)
    (w : Option watchdog_helper.watchdog.WatchPoint)
    (r : core.result.Result (Option KeyDesc) anyhow.Error)
    (hwatch : watchdog_helper.watchdog.watch (toStr "KeystoreDB::load_key_descriptor") = ok w)
    (hwt : database.KeystoreDB.with_transaction descriptorFn self
      database.TransactionBehavior.Deferred key_id = ok (r, self1))
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (hctx : AnyCtxLaw root (Option KeyDesc)) :
    ∃ r1, database.KeystoreDB.load_key_descriptor self key_id = ok (r1, self1) ∧
      ContextOutcome root r r1

end LoadKeyDescriptor

section Pragma
open alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open rusqlite.types.from_sql renaming FromSql → FromSqlTrait
open database.KeystoreDB.pragma.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0RowResultTError → pragmaRow

recall pragma_value (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) {T : Type _}
    (inst : FromSqlTrait T) (self : database.KeystoreDB) (nm : Str)
    (v : T)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hquery : rusqlite.Connection.query_row Tuple.Insts.RusqliteParamsParams
      (pragmaRow inst) self.conn sv () () = ok (.Ok v))
    (hctx : RusqliteCtxLaw rootSql root T) :
    database.KeystoreDB.pragma inst self nm = ok (.Ok v, self)

recall pragma_error (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) {T : Type _}
    (inst : FromSqlTrait T) (self : database.KeystoreDB) (nm : Str)
    (x : rusqlite.error.Error)
    (hfmt : AllocFmtFormatSpec) (s : String) (sv : Str)
    (hq : alloc.fmt.format () = ok s) (hsd : stringDeref s = ok sv)
    (hquery : rusqlite.Connection.query_row Tuple.Insts.RusqliteParamsParams
      (pragmaRow inst) self.conn sv () () = ok (.Err x))
    (hctx : RusqliteCtxLaw rootSql root T) :
    ∃ e, database.KeystoreDB.pragma inst self nm = ok (.Err e, self) ∧
      root e = rootSql x

end Pragma

end Keystore2Verify.DatabaseKeystoreDb
