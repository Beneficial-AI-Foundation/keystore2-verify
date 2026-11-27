import Keystore2Verify.Specs.Defs.DatabaseKeystoreDb

namespace Keystore2Verify.DatabaseKeystoreDb
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.ops.function renaming Fn → FnTrait
open std.thread.functions renaming sleep → threadSleep
open Keystore2Verify.Permission (KeyDesc)

/-! `load_key_entry` calls `load_key_entry_internal` in a loop. Its outcome is an inline
hypothesis in each theorem. In the Rust source the permission callback `check_permission` is not
called in this function: it is passed on to `load_key_entry_internal`. The loop has no bound on
the number of retries, so no theorem says that it ends: the three theorems say what one pass of
the loop does. -/

/-- conditional: if `load_key_entry_internal` returns `Ok x` and the database `self1`, the result
is that same `Ok x` and `self1`, with no context added. In the Rust source this branch returns
without calling `sleep`. Hypotheses: `watch` returns; the call returns `(Ok x, self1)`. -/
theorem load_key_entry_success {T0 : Type _}
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
      check_permission = ok (.Ok x, self1) := by
  sorry

/-- conditional: if `load_key_entry_internal` returns an error `e` that is not a "database locked"
error, the result is an `Err e'` with the same root cause as `e`, and the database `self1` that the
failing call returned. In the Rust source this path returns at once, without waiting or retrying.
Hypotheses: `watch` returns; the call returns `(Err e, self1)`; `is_locked_error e` returns `false`;
`format` and `from_str_nonconst` do not panic; the `context` assumption for `anyhow::Error`. -/
theorem load_key_entry_other_error (root : anyhow.Error → ErrRoot) {T0 : Type _}
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
        check_permission = ok (.Err e', self1) ∧ root e' = root e := by
  sorry

/-- conditional: if `load_key_entry_internal` returns a "database locked" error, the function waits
for the retry interval and goes on from the database `self1` that the failing call returned (not
from `self`): its result is the result of the loop continued from `self1`. In the Rust source the
watchdog is created once, before the loop, so the loop is continued and the public method is not
started again. Hypotheses: `watch` returns; the call returns `(Err e, self1)`; `is_locked_error e`
returns `true`; the retry interval `DB_BUSY_RETRY_INTERVAL` evaluates to `d`; `sleep d` returns. -/
theorem load_key_entry_locked_retry {T0 : Type _}
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
      caller_uid := by
  sorry
