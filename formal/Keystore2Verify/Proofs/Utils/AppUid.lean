import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open rustutils.android.users renaming multiuser_get_user_id → multiuserGetUserId
open utils.AppUid.Insts
open CoreCmpPartialEqAppUid renaming eq → appUidEq
open CoreCloneClone renaming clone → appUidClone
open CoreCmpOrd renaming cmp → appUidCmp
open CoreCmpPartialOrdAppUid renaming partial_cmp → appUidPartialCmp

/-- exact: `AppUid::eq` never fails and returns `true` exactly when the two numbers
are equal. -/
theorem appUid_eq (x y : utils.AppUid) :
    appUidEq x y = ok (decide (x = y)) := by
  sorry

/-- exact: `AppUid::clone` never fails and returns its argument. -/
theorem appUid_clone (x : utils.AppUid) : appUidClone x = ok x := by
  sorry

/-- exact: `AppUid::cmp` never fails. It compares the two numbers as signed integers. -/
theorem appUid_cmp (x y : utils.AppUid) :
    appUidCmp x y = ok (compare x.val y.val) := by
  sorry

/-- exact: `AppUid::partial_cmp` never fails and returns `Some` of the signed comparison of
the two numbers. -/
theorem appUid_partial_cmp (x y : utils.AppUid) :
    appUidPartialCmp x y = ok (some (compare x.val y.val)) := by
  sorry

/-- conditional: let `i` be the low 32 bits of the uid (the uid modulo 2^32, as for Rust's
`as u32`). If `multiuser_get_user_id i = ok u`, then `AppUid::owning_user` returns the `u32`
`u` read as an `i32`: `u` if `u < 2^31`, and `u - 2^32` otherwise. Hypotheses: the outcome
of the external call (`hcall`), for the number `i` with `i = uid mod 2^32` (`hi`). -/
theorem AppUid_owning_user (self : utils.AppUid) (i u : Std.U32)
    (hi : (i.val : Int) = self.val % 2 ^ 32)
    (hcall : multiuserGetUserId i = ok u) :
    ∃ r, utils.AppUid.owning_user self = ok r ∧
      r.val = if u.val < 2 ^ 31 then (u.val : Int) else (u.val : Int) - 2 ^ 32 := by
  sorry

/-- conditional: if `ThreadState::get_calling_uid` returns `ok u`, then `AppUid::calling`
returns the same number as an `i64`, so a value in `[0, 2^32)`. Hypothesis: the outcome of
the external call (`hcall`). -/
theorem AppUid_calling (u : Std.U32) (hcall : binder.ThreadState.get_calling_uid = ok u) :
    ∃ r, utils.AppUid.calling = ok r ∧ r.val = u.val := by
  sorry

end Keystore2Verify.Utils
