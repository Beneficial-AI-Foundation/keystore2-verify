import Keystore2Verify.Specs.Defs.DatabasePerboot

namespace Keystore2Verify.DatabasePerboot
open Aeneas Aeneas.Std Result keystore2
open keystore2.std.sync.poison.rwlock
open keystore2.std.collections.hash.set
open database.perboot
open PerbootDB.Insts.CoreDefaultDefault renaming «default» → perbootDefault
open RwLock.Insts.CoreDefaultDefault renaming «default» → rwLockDefault
open RwLockWriteGuard.Insts.CoreOpsDerefDerefMut renaming deref_mut → guardDerefMut
open RwLockReadGuard.Insts.CoreOpsDerefDeref renaming deref → guardDeref
open keystore2.std.hash.random.RandomState.Insts
open keystore2.std.sync.poison
open std.hash.random
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr

/-- The set type of the field `auth_tokens`. -/
abbrev TokenSet : Type :=
  HashSet AuthTokenEntryWrap RandomState alloc.alloc.Global

/-- conditional: if the default of the lock around the default (empty) set returns `rl`, `default`
returns the database with the lock `rl`. Hypothesis: that call returns `ok rl`. The translation
cannot say that the set is empty. -/
theorem perboot_db_default_ok (rl : RwLock TokenSet)
    (h : rwLockDefault (HashSetTSGlobal.Insts.CoreDefaultDefault AuthTokenEntryWrap
      CoreDefaultDefault) = ok rl) :
    perbootDefault = ok { auth_tokens := rl } := by
  sorry

/-- conditional: if the default of the lock fails with `e`, `default` fails with `e`. Hypothesis:
that call returns `fail e`. -/
theorem perboot_db_default_fail (e : Error)
    (h : rwLockDefault (HashSetTSGlobal.Insts.CoreDefaultDefault AuthTokenEntryWrap
      CoreDefaultDefault) = fail e) :
    perbootDefault = fail e := by
  sorry

/-- exact: `new` is the derived `default`. -/
theorem perboot_db_new : PerbootDB.new = perbootDefault := by
  sorry

/-- conditional: if taking the write lock gives a guard `g`, the guard gives access to the set
`hs`, and `replace` returns `ok r`, then `insert_auth_token_entry` returns `ok ()`. Hypotheses:
the three calls return as stated. The translation drops the new set that `replace` produces, so
no statement can say that the set now holds `entry`. -/
theorem perboot_db_insert_auth_token_entry_ok (self : PerbootDB) (entry : database.AuthTokenEntry)
    (g : RwLockWriteGuard TokenSet) (hs : TokenSet) (back : TokenSet → RwLockWriteGuard TokenSet)
    (r : Option AuthTokenEntryWrap × TokenSet)
    (hw : RwLock.write self.auth_tokens = ok (ROk g))
    (hd : guardDerefMut g = ok (hs, back))
    (hr : HashSet.replace AuthTokenEntryWrap.Insts.CoreCmpEq AuthTokenEntryWrap.Insts.CoreHashHash
      CoreHashBuildHasherDefaultHasher hs entry = ok r) :
    PerbootDB.insert_auth_token_entry self entry = ok () := by
  sorry

/-- conditional: if the write lock is poisoned, `insert_auth_token_entry` panics. This is the
`unwrap` on line 86 of the Rust source. Hypothesis: `write` returns `ok (Err p)`. -/
theorem perboot_db_insert_auth_token_entry_poisoned (self : PerbootDB)
    (entry : database.AuthTokenEntry) (p : PoisonError (RwLockWriteGuard TokenSet))
    (hw : RwLock.write self.auth_tokens = ok (RErr p)) :
    PerbootDB.insert_auth_token_entry self entry = fail Error.panic := by
  sorry

/-- conditional: if `write` fails with `e`, `insert_auth_token_entry` fails with `e`. Hypothesis:
`write` returns `fail e`. -/
theorem perboot_db_insert_auth_token_entry_write_fails (self : PerbootDB)
    (entry : database.AuthTokenEntry) (e : Error)
    (hw : RwLock.write self.auth_tokens = fail e) :
    PerbootDB.insert_auth_token_entry self entry = fail e := by
  sorry

/-- conditional: if `write` gives a guard `g` and `deref_mut` fails with `e`,
`insert_auth_token_entry` fails with `e`. Hypotheses: the two calls return as stated. -/
theorem perboot_db_insert_auth_token_entry_deref_fails (self : PerbootDB)
    (entry : database.AuthTokenEntry) (g : RwLockWriteGuard TokenSet) (e : Error)
    (hw : RwLock.write self.auth_tokens = ok (ROk g))
    (hd : guardDerefMut g = fail e) :
    PerbootDB.insert_auth_token_entry self entry = fail e := by
  sorry

/-- conditional: if `write` gives a guard `g`, `deref_mut` gives the set `hs` and `replace` fails
with `e`, `insert_auth_token_entry` fails with `e`. Hypotheses: the three calls return as
stated. -/
theorem perboot_db_insert_auth_token_entry_replace_fails (self : PerbootDB)
    (entry : database.AuthTokenEntry) (g : RwLockWriteGuard TokenSet) (hs : TokenSet)
    (back : TokenSet → RwLockWriteGuard TokenSet) (e : Error)
    (hw : RwLock.write self.auth_tokens = ok (ROk g))
    (hd : guardDerefMut g = ok (hs, back))
    (hr : HashSet.replace AuthTokenEntryWrap.Insts.CoreCmpEq AuthTokenEntryWrap.Insts.CoreHashHash
      CoreHashBuildHasherDefaultHasher hs entry = fail e) :
    PerbootDB.insert_auth_token_entry self entry = fail e := by
  sorry

/-- conditional: if taking the read lock gives a guard `g`, the guard gives access to the set `hs`
and `len hs` returns `n`, then `auth_tokens_len` returns `n`. Hypotheses: the three calls return as
stated. Nothing relates `n` to the entries that `insert_auth_token_entry` stored. -/
theorem perboot_db_auth_tokens_len_ok (self : PerbootDB) (g : RwLockReadGuard TokenSet)
    (hs : TokenSet) (n : Std.Usize)
    (hr : RwLock.read self.auth_tokens = ok (ROk g))
    (hd : guardDeref g = ok hs) (hl : HashSet.len hs = ok n) :
    PerbootDB.auth_tokens_len self = ok n := by
  sorry

/-- conditional: if the read lock is poisoned, `auth_tokens_len` panics. This is the `unwrap` on
line 101 of the Rust source. Hypothesis: `read` returns `ok (Err p)`. -/
theorem perboot_db_auth_tokens_len_poisoned (self : PerbootDB)
    (p : PoisonError (RwLockReadGuard TokenSet))
    (hr : RwLock.read self.auth_tokens = ok (RErr p)) :
    PerbootDB.auth_tokens_len self = fail Error.panic := by
  sorry

/-- conditional: if `read` fails with `e`, `auth_tokens_len` fails with `e`. Hypothesis: `read`
returns `fail e`. -/
theorem perboot_db_auth_tokens_len_read_fails (self : PerbootDB) (e : Error)
    (hr : RwLock.read self.auth_tokens = fail e) :
    PerbootDB.auth_tokens_len self = fail e := by
  sorry

/-- conditional: if `read` gives a guard `g` and `deref` fails with `e`, `auth_tokens_len` fails
with `e`. Hypotheses: the two calls return as stated. -/
theorem perboot_db_auth_tokens_len_deref_fails (self : PerbootDB) (g : RwLockReadGuard TokenSet)
    (e : Error) (hr : RwLock.read self.auth_tokens = ok (ROk g))
    (hd : guardDeref g = fail e) :
    PerbootDB.auth_tokens_len self = fail e := by
  sorry

/-- conditional: if `read` gives a guard `g`, `deref` gives the set `hs` and `len hs` fails with
`e`, `auth_tokens_len` fails with `e`. Hypotheses: the three calls return as stated. -/
theorem perboot_db_auth_tokens_len_len_fails (self : PerbootDB) (g : RwLockReadGuard TokenSet)
    (hs : TokenSet) (e : Error)
    (hr : RwLock.read self.auth_tokens = ok (ROk g))
    (hd : guardDeref g = ok hs) (hl : HashSet.len hs = fail e) :
    PerbootDB.auth_tokens_len self = fail e := by
  sorry

end Keystore2Verify.DatabasePerboot
