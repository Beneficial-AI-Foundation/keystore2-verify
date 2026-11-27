import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.sync.Arc.Insts.CoreOpsDerefDeref renaming deref → arcDeref
open database.perboot.PerbootDB renaming auth_tokens_len → authTokensLen

open android_security_metrics.aidl.android.security.metrics

/-! In the translation `wd::watch_millis_with` is a function that returns `none` and never
fails (the file `watchdog_helper.rs` is translated for the build without the Android watchdog).
So the statements below need no hypothesis about it. -/

/-- exact: for `Storage::DATABASE` (15) the result, and the returned database, are those of
`get_total_size`. -/
theorem get_storage_stat_database (self : database.KeystoreDB) (st : Storage.Storage)
    (h : st.val = storageDatabase) :
    database.KeystoreDB.get_storage_stat self st = database.KeystoreDB.get_total_size self := by
  sorry

/-- exact: for the twelve storage types of a table or an index (1 to 10, 12 and 13), `t` is the
name given by `storageTableName`. The result, and the returned database, are those of
`get_table_size` for the same storage type, the schema `persistent` and the table `t`. -/
theorem get_storage_stat_table (self : database.KeystoreDB) (st : Storage.Storage) (t : Str)
    (h : storageTableName st.val = some t) :
    database.KeystoreDB.get_storage_stat self st =
      database.KeystoreDB.get_table_size self st (toStr "persistent") t := by
  sorry

/-- conditional: for `Storage::AUTH_TOKEN` (11), the database is returned unchanged and the result
is `Ok` of statistics with this storage type, `unused_size` zero, and `size` equal to the
number of token entries `n` times the size `sz` of an entry, cut to 32 bits (`as i32`, which wraps).
Hypotheses: `deref` of the shared per-boot state returns `pd`; `auth_tokens_len pd` returns
`n` (the read lock is not poisoned); `size_of::<AuthTokenEntry>()` returns `sz`; the product fits
in a `usize`. -/
theorem get_storage_stat_auth_token (self : database.KeystoreDB) (st : Storage.Storage)
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
      stats.size.bv = BitVec.ofNat 32 (n.val * sz.val) := by
  sorry

/-- conditional: for `Storage::AUTH_TOKEN` (11), if the product of `n` and `sz` does not fit in a
`usize`, the function fails with an integer overflow (a panic in debug builds of the Rust source).
Hypotheses as in `get_storage_stat_auth_token`, except the last. -/
theorem get_storage_stat_auth_token_overflow (self : database.KeystoreDB) (st : Storage.Storage)
    (pd : database.perboot.PerbootDB) (n sz : Std.Usize)
    (h : st.val = storageAuthToken)
    (hderef : arcDeref alloc.alloc.Global self.perboot =
      ok pd)
    (hlen : authTokensLen pd = ok n)
    (hsz : core.mem.size_of database.AuthTokenEntry = ok sz)
    (hover : Std.Usize.max < n.val * sz.val) :
    database.KeystoreDB.get_storage_stat self st = fail Error.integerOverflow := by
  sorry

/-- conditional: for `Storage::AUTH_TOKEN` (11), if `auth_tokens_len` fails with `err`, the function
fails with the same `err`, and `size_of` and the multiplication are not needed. In the Rust source
this includes the panic on a poisoned read lock; `err` can also come from another failure inside
that helper. Hypothesis: `deref` of the shared per-boot state returns `pd`. -/
theorem get_storage_stat_auth_token_len_failure (self : database.KeystoreDB)
    (st : Storage.Storage) (pd : database.perboot.PerbootDB) (err : Error)
    (h : st.val = storageAuthToken)
    (hderef : arcDeref alloc.alloc.Global self.perboot = ok pd)
    (hlen : authTokensLen pd = fail err) :
    database.KeystoreDB.get_storage_stat self st = fail err := by
  sorry

/-- conditional: for a storage type that is neither `DATABASE`, nor `AUTH_TOKEN`, nor a table or
an index (0, 14, 16 and every other number), the result is an `Err` whose root cause is a plain
message, and the database is returned unchanged. Hypotheses: `format` does not panic
(`AllocFmtFormatSpec`), and the assumption about `anyhow::Error::msg`. -/
theorem get_storage_stat_unsupported (root : anyhow.Error → ErrRoot)
    (self : database.KeystoreDB) (st : Storage.Storage)
    (hdb : st.val ≠ storageDatabase) (hauth : st.val ≠ storageAuthToken)
    (htab : storageTableName st.val = none)
    (hfmt : AllocFmtFormatSpec) (hmsg : AnyhowErrorMsgSpec root) :
    ∃ e, database.KeystoreDB.get_storage_stat self st = ok (.Err e, self) ∧
      root e = ErrRoot.other := by
  sorry
