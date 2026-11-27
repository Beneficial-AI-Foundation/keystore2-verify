import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
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

/-- exact: `db_tag` never fails. It returns the number of the variant, in the order of the
declaration: `EncryptedBy` 0, `Salt` 1, `Iv` 2, `AeadTag` 3, `KmUuid` 4, `PublicKey` 5,
`MaxBootLevel` 6. The payload is ignored. -/
theorem blob_meta_entry_db_tag :
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.EncryptedBy x) = ok 0#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.Salt x) = ok 1#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.Iv x) = ok 2#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.AeadTag x) = ok 3#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.KmUuid x) = ok 4#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.PublicKey x) = ok 5#i64) ∧
    (∀ x, blobMetaEntryDbTag (database.BlobMetaEntry.MaxBootLevel x) = ok 6#i64) := by
  sorry

/-- conditional: `new_from_sql` for the number 0 (`EncryptedBy`). If the column read returns `Ok v`,
the result is `Ok (EncryptedBy v)`. If it returns an error `e`, the result is an error whose
root cause is the root cause of the `rusqlite` error `e`: its class is `rootSql e`. Hypotheses:
`RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls both).
The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_encrypted_by
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.EncryptedBy) rootSql root
      fnOnce0)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet encryptedByFromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 0#i64 data = ok (.Ok (.EncryptedBy v))) ∧
    (∀ e, sqlFieldGet encryptedByFromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 0#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 1 (`Salt`). If the column read returns `Ok v`, the
result is `Ok (Salt v)`. If it returns an error `e`, the result is an error whose root cause is
the root cause of the `rusqlite` error `e`: its class is `rootSql e`. Hypotheses:
`RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls both).
The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_salt
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce1)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 1#i64 data = ok (.Ok (.Salt v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 1#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 2 (`Iv`). If the column read returns `Ok v`, the
result is `Ok (Iv v)`. If it returns an error `e`, the result is an error whose root cause is
the root cause of the `rusqlite` error `e`: its class is `rootSql e`. Hypotheses:
`RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls both).
The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_iv
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce2)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 2#i64 data = ok (.Ok (.Iv v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 2#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 3 (`AeadTag`). If the column read returns `Ok v`, the
result is `Ok (AeadTag v)`. If it returns an error `e`, the result is an error whose root cause
is the root cause of the `rusqlite` error `e`: its class is `rootSql e`. Hypotheses:
`RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls both).
The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_aead_tag
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce3)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 3#i64 data = ok (.Ok (.AeadTag v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 3#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 4 (`KmUuid`). If the column read returns `Ok v`, the
result is `Ok (KmUuid v)`. If it returns an error `e`, the result is an error whose root cause
is the root cause of the `rusqlite` error `e`: its class is `rootSql e`. Hypotheses:
`RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls both).
The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_km_uuid
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.Uuid) rootSql root
      fnOnce4)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet uuidFromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 4#i64 data = ok (.Ok (.KmUuid v))) ∧
    (∀ e, sqlFieldGet uuidFromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 4#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 5 (`PublicKey`). If the column read returns `Ok v`,
the result is `Ok (PublicKey v)`. If it returns an error `e`, the result is an error whose root
cause is the root cause of the `rusqlite` error `e`: its class is `rootSql e`. Hypotheses:
`RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls both).
The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_public_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce5)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 5#i64 data = ok (.Ok (.PublicKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 5#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 6 (`MaxBootLevel`). If the column read returns `Ok
v`, the result is `Ok (MaxBootLevel v)`. If it returns an error `e`, the result is an error
whose root cause is the root cause of the `rusqlite` error `e`: its class is `rootSql e`.
Hypotheses: `RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec`
and `CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls
both). The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem blob_meta_entry_new_from_sql_max_boot_level
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := Std.I32) rootSql root
      fnOnce6)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet i32FromSql data = ok (.Ok v) →
      blobMetaEntryNewFromSql 6#i64 data = ok (.Ok (.MaxBootLevel v))) ∧
    (∀ e, sqlFieldGet i32FromSql data = ok (.Err e) →
      ∃ e', blobMetaEntryNewFromSql 6#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for a number that is not the number of a variant (below 0 or above
6) returns an error. In the Rust source this branch does not read the column. The error comes
from `anyhow!` and has a root cause that is none of the classified types: its class is `other`.
Hypotheses: `AllocFmtFormatSpec`, `AnyhowAdhocNewSpec` and `AnyhowMustUseSpec`. -/
theorem blob_meta_entry_new_from_sql_unknown_tag
    (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hnew : AnyhowAdhocNewSpec root)
    (hmu : AnyhowMustUseSpec)
    (tag : Std.I64) (data : database.utils.SqlField) (h : tag.val < 0 ∨ 6 < tag.val) :
    ∃ e, blobMetaEntryNewFromSql tag data = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two entries are the same variant
with equal payloads. -/
theorem blob_meta_entry_eq (a b : database.BlobMetaEntry) :
    ∃ r, blobMetaEntryEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- conditional: when the two entries are different variants (hypothesis: the positions of the
variants differ), `cmp` never fails and compares the position of the variants. No assumption
about an external function is needed. -/
theorem blob_meta_entry_cmp_variants (a b : database.BlobMetaEntry)
    (h : blobMetaEntryRank a ≠ blobMetaEntryRank b) :
    blobMetaEntryCmpFn a b = ok (compare (blobMetaEntryRank a) (blobMetaEntryRank b)) := by
  sorry

/-- conditional: `cmp` returns the order of the variants, and for equal variants the order of the
payloads (numbers as signed numbers, byte sequences lexicographically). Hypotheses:
`VecU8CmpSpec` and `ArrayU8Cmp16Spec` (the `KmUuid` payload is a 16-byte array). -/
theorem blob_meta_entry_cmp (h : VecU8CmpSpec) (harr : ArrayU8Cmp16Spec)
    (a b : database.BlobMetaEntry) :
    blobMetaEntryCmpFn a b = ok (blobMetaEntryCmp a b) := by
  sorry

/-- exact: `partial_cmp` returns `Some` of whatever `cmp` returns, and fails exactly when `cmp`
fails. -/
theorem blob_meta_entry_partial_cmp (a b : database.BlobMetaEntry) :
    (∀ o, blobMetaEntryCmpFn a b = ok o → blobMetaEntryPartialCmp a b = ok (some o)) ∧
    (∀ f, blobMetaEntryCmpFn a b = fail f → blobMetaEntryPartialCmp a b = fail f) := by
  sorry
