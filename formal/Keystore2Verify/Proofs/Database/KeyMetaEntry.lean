import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
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

/-- exact: `db_tag` never fails. It returns the number of the variant, in the order of the
declaration: `CreationDate` 0, `AttestationExpirationDate` 1, `AttestationMacedPublicKey` 2,
`AttestationRawPubKey` 3, `Sec1PublicKey` 4. The payload is ignored. -/
theorem key_meta_entry_db_tag :
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.CreationDate x) = ok 0#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.AttestationExpirationDate x) = ok 1#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.AttestationMacedPublicKey x) = ok 2#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.AttestationRawPubKey x) = ok 3#i64) ∧
    (∀ x, keyMetaEntryDbTag (database.KeyMetaEntry.Sec1PublicKey x) = ok 4#i64) := by
  sorry

/-- conditional: `new_from_sql` for the number 0 (`CreationDate`). If the column read returns `Ok
v`, the result is `Ok (CreationDate v)`. If it returns an error `e`, the result is an error
whose root cause is the root cause of the `rusqlite` error `e`: its class is `rootSql e`.
Hypotheses: `RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec`
and `CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls
both). The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem key_meta_entry_new_from_sql_creation_date
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.DateTime) rootSql root
      fnOnce0)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet dateTimeFromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 0#i64 data = ok (.Ok (.CreationDate v))) ∧
    (∀ e, sqlFieldGet dateTimeFromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 0#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 1 (`AttestationExpirationDate`). If the column read
returns `Ok v`, the result is `Ok (AttestationExpirationDate v)`. If it returns an error `e`,
the result is an error whose root cause is the root cause of the `rusqlite` error `e`: its class
is `rootSql e`. Hypotheses: `RusqliteWithContextAssumption` at this call of `with_context`,
`AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the
context message calls both). The column read `SqlField::get` is an inline outcome hypothesis in
each part. -/
theorem key_meta_entry_new_from_sql_attestation_expiration_date
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := database.DateTime) rootSql root
      fnOnce1)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet dateTimeFromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 1#i64 data = ok (.Ok (.AttestationExpirationDate v))) ∧
    (∀ e, sqlFieldGet dateTimeFromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 1#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 2 (`AttestationMacedPublicKey`). If the column read
returns `Ok v`, the result is `Ok (AttestationMacedPublicKey v)`. If it returns an error `e`,
the result is an error whose root cause is the root cause of the `rusqlite` error `e`: its class
is `rootSql e`. Hypotheses: `RusqliteWithContextAssumption` at this call of `with_context`,
`AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the
context message calls both). The column read `SqlField::get` is an inline outcome hypothesis in
each part. -/
theorem key_meta_entry_new_from_sql_attestation_maced_public_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce2)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 2#i64 data = ok (.Ok (.AttestationMacedPublicKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 2#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 3 (`AttestationRawPubKey`). If the column read
returns `Ok v`, the result is `Ok (AttestationRawPubKey v)`. If it returns an error `e`, the
result is an error whose root cause is the root cause of the `rusqlite` error `e`: its class is
`rootSql e`. Hypotheses: `RusqliteWithContextAssumption` at this call of `with_context`,
`AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the
context message calls both). The column read `SqlField::get` is an inline outcome hypothesis in
each part. -/
theorem key_meta_entry_new_from_sql_attestation_raw_pub_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce3)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 3#i64 data = ok (.Ok (.AttestationRawPubKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 3#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for the number 4 (`Sec1PublicKey`). If the column read returns `Ok
v`, the result is `Ok (Sec1PublicKey v)`. If it returns an error `e`, the result is an error
whose root cause is the root cause of the `rusqlite` error `e`: its class is `rootSql e`.
Hypotheses: `RusqliteWithContextAssumption` at this call of `with_context`, `AllocFmtFormatSpec`
and `CoreFmtArgumentsFromStrNonconstSpec` (the closure that builds the context message calls
both). The column read `SqlField::get` is an inline outcome hypothesis in each part. -/
theorem key_meta_entry_new_from_sql_sec1_public_key
    (rootSql : rusqlite.error.Error → ErrRoot) (root : anyhow.Error → ErrRoot)
    (hctx : RusqliteWithContextAssumption (T := alloc.vec.Vec Std.U8) rootSql root
      fnOnce4)
    (hfmt : AllocFmtFormatSpec) (hargs : CoreFmtArgumentsFromStrNonconstSpec)
    (data : database.utils.SqlField) :
    (∀ v, sqlFieldGet vecU8FromSql data = ok (.Ok v) →
      keyMetaEntryNewFromSql 4#i64 data = ok (.Ok (.Sec1PublicKey v))) ∧
    (∀ e, sqlFieldGet vecU8FromSql data = ok (.Err e) →
      ∃ e', keyMetaEntryNewFromSql 4#i64 data = ok (.Err e') ∧ root e' = rootSql e) := by
  sorry

/-- conditional: `new_from_sql` for a number that is not the number of a variant (below 0 or above
4) returns an error. In the Rust source this branch does not read the column. The error comes
from `anyhow!` and has a root cause that is none of the classified types: its class is `other`.
Hypotheses: `AllocFmtFormatSpec`, `AnyhowAdhocNewSpec` and `AnyhowMustUseSpec`. -/
theorem key_meta_entry_new_from_sql_unknown_tag
    (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hnew : AnyhowAdhocNewSpec root)
    (hmu : AnyhowMustUseSpec)
    (tag : Std.I64) (data : database.utils.SqlField) (h : tag.val < 0 ∨ 4 < tag.val) :
    ∃ e, keyMetaEntryNewFromSql tag data = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two entries are the same variant
with equal payloads. -/
theorem key_meta_entry_eq (a b : database.KeyMetaEntry) :
    ∃ r, keyMetaEntryEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- conditional: when the two entries are different variants (hypothesis: the positions of the
variants differ), `cmp` never fails and compares the position of the variants. No assumption
about an external function is needed. -/
theorem key_meta_entry_cmp_variants (a b : database.KeyMetaEntry)
    (h : keyMetaEntryRank a ≠ keyMetaEntryRank b) :
    keyMetaEntryCmpFn a b = ok (compare (keyMetaEntryRank a) (keyMetaEntryRank b)) := by
  sorry

/-- conditional: `cmp` returns the order of the variants, and for equal variants the order of the
payloads (numbers as signed numbers, byte sequences lexicographically). Hypotheses:
`VecU8CmpSpec`. -/
theorem key_meta_entry_cmp (h : VecU8CmpSpec)
    (a b : database.KeyMetaEntry) :
    keyMetaEntryCmpFn a b = ok (keyMetaEntryCmp a b) := by
  sorry

/-- exact: `partial_cmp` returns `Some` of whatever `cmp` returns, and fails exactly when `cmp`
fails. -/
theorem key_meta_entry_partial_cmp (a b : database.KeyMetaEntry) :
    (∀ o, keyMetaEntryCmpFn a b = ok o → keyMetaEntryPartialCmp a b = ok (some o)) ∧
    (∀ f, keyMetaEntryCmpFn a b = fail f → keyMetaEntryPartialCmp a b = fail f) := by
  sorry
