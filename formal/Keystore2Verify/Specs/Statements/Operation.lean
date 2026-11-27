import Keystore2Verify.Proofs.Operation.UpdateOutcome
import Keystore2Verify.Proofs.Operation.CheckInputLength
import Keystore2Verify.Proofs.Operation.OperationDbGet

namespace Keystore2Verify.Operation

section UpdateOutcome
open Aeneas Aeneas.Std Result keystore2
open android_system_keystore2.aidl.android.system.keystore2
open operation.Operation renaming update_outcome → updateOutcome

recall update_outcome_ok {T : Type} (self : operation.Operation) (o : operation.Outcome)
    (v : T) :
    updateOutcome self o (.Ok v) = ok (.Ok v, o)

recall update_outcome_err {T : Type} (self : operation.Operation) (o : operation.Outcome)
    (e : error.Error) :
    ∃ se, updateOutcome self o (.Err e : core.result.Result T error.Error) =
        ok (.Err e, .ErrorCode se) ∧
      (∀ r, e = .Rc r → se = r) ∧ (∀ ec, e = .Km ec → se = ec) ∧
      (∀ a b, e = .Binder a b → se = ResponseCode.ResponseCode.SYSTEM_ERROR) ∧
      (∀ a, e = .BinderTransaction a → se = ResponseCode.ResponseCode.SYSTEM_ERROR)

end UpdateOutcome

section CheckInputLength
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open operation.Operation renaming check_input_length → checkInputLength

recall check_input_length_ok (data : Slice Std.U8) (h : data.length ≤ 32768) :
    checkInputLength data = ok (.Ok ())

recall check_input_length_too_long (root : anyhow.Error → ErrRoot)
    (hnew : AnyhowKindTraitNewSpec root) (hmust : AnyhowMustUseSpec)
    (rc : ResponseCode.ResponseCode)
    (hrc : ResponseCode.ResponseCode.TOO_MUCH_DATA = ok rc)
    (data : Slice Std.U8) (h : 32768 < data.length) :
    ∃ e, checkInputLength data = ok (.Err e) ∧ root e = ErrRoot.ks (error.Error.Rc rc)

end CheckInputLength

section OperationDbGet
open Aeneas Aeneas.Std Result keystore2
open operation.OperationDb renaming get → operationDbGet
open std.sync.poison.mutex

recall operation_db_get_slot (hand : OptionAndThenSpec)
    (self : operation.OperationDb) (index : Std.Usize)
    (mg : MutexGuard (alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global)))
    (hlock : Mutex.lock self.operations = ok (.Ok mg))
    (v : alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global))
    (hderef : MutexGuard.Insts.CoreOpsDerefDeref.deref mg = ok v)
    (w : alloc.sync.Weak operation.Operation alloc.alloc.Global)
    (hw : v.val[index.val]? = some w) :
    operationDbGet self index =
      alloc.sync.Weak.upgrade alloc.alloc.Global.Insts.CoreAllocAllocatorClone w

recall operation_db_get_out_of_range (hand : OptionAndThenSpec)
    (self : operation.OperationDb) (index : Std.Usize)
    (mg : MutexGuard (alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global)))
    (hlock : Mutex.lock self.operations = ok (.Ok mg))
    (v : alloc.vec.Vec (alloc.sync.Weak operation.Operation alloc.alloc.Global))
    (hderef : MutexGuard.Insts.CoreOpsDerefDeref.deref mg = ok v)
    (hw : v.val.length ≤ index.val) :
    operationDbGet self index = ok none

recall operation_db_get_poisoned (self : operation.OperationDb) (index : Std.Usize)
    (pe : std.sync.poison.PoisonError (MutexGuard (alloc.vec.Vec (alloc.sync.Weak
      operation.Operation alloc.alloc.Global))))
    (hlock : Mutex.lock self.operations = ok (.Err pe)) :
    operationDbGet self index = fail Error.panic

end OperationDbGet

end Keystore2Verify.Operation
