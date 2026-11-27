import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
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

/-- exact: `clone` never fails and returns its argument. -/
theorem boot_time_clone (x : database.BootTime) : bootTimeClone x = ok x := by
  sorry

/-- exact: `default` never fails and returns 0. -/
theorem boot_time_default : bootTimeDefault = ok 0#i64 := by
  sorry

/-- exact: `eq` never fails. It returns `true` exactly when the two millisecond counts are
equal. -/
theorem boot_time_eq (a b : database.BootTime) :
    ∃ r, bootTimeEq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

/-- exact: `cmp` never fails. It compares the two millisecond counts as signed numbers. -/
theorem boot_time_cmp (a b : database.BootTime) :
    bootTimeCmp a b = ok (compare a.val b.val) := by
  sorry

/-- exact: `partial_cmp` never fails and returns `Some` of the result of `cmp`. -/
theorem boot_time_partial_cmp (a b : database.BootTime) :
    bootTimePartialCmp a b = ok (some (compare a.val b.val)) := by
  sorry

/-- conditional: `BootTime::now` returns what `get_current_time_in_milliseconds` returned. The
function `get_current_time_in_milliseconds` is an item of keystore2 that the extraction could not
translate (blocked by extraction). Hypothesis: it returned `t`. -/
theorem boot_time_now (t : Std.I64) (h : utils.get_current_time_in_milliseconds = ok t) :
    bootTimeNow = ok t := by
  sorry

/-- exact: `milliseconds` never fails and returns the stored number. -/
theorem boot_time_milliseconds (x : database.BootTime) : bootTimeMilliseconds x = ok x := by
  sorry

/-- exact: `seconds` never fails. It returns the number of milliseconds divided by 1000, rounded
towards zero. -/
theorem boot_time_seconds (x : database.BootTime) :
    ∃ r, bootTimeSeconds x = ok r ∧ r.val = Int.tdiv x.val 1000 := by
  sorry

/-- conditional: `checked_sub` never fails. Restriction: the difference of the two numbers fits
in an `i64` (between `i64::MIN` and `i64::MAX`). Then it returns the difference. -/
theorem boot_time_checked_sub_some (a b : database.BootTime)
    (h : Std.I64.min ≤ a.val - b.val ∧ a.val - b.val ≤ Std.I64.max) :
    ∃ r, bootTimeCheckedSub a b = ok (some r) ∧ r.val = a.val - b.val := by
  sorry

/-- conditional: `checked_sub` returns `None`. Restriction: the difference of the two numbers does
not fit in an `i64` (it is below `i64::MIN` or above `i64::MAX`). -/
theorem boot_time_checked_sub_none (a b : database.BootTime)
    (h : a.val - b.val < Std.I64.min ∨ Std.I64.max < a.val - b.val) :
    bootTimeCheckedSub a b = ok none := by
  sorry
