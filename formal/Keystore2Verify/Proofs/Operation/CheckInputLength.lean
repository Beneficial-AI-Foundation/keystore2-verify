import Keystore2Verify.Specs.Defs.Operation

namespace Keystore2Verify.Operation
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open operation.Operation renaming check_input_length → checkInputLength

/-- exact: an input of at most `MAX_RECEIVE_DATA` = 32768 bytes (including the empty input) is
accepted: `check_input_length` returns `Ok ()`. -/
theorem check_input_length_ok (data : Slice Std.U8) (h : data.length ≤ 32768) :
    checkInputLength data = ok (.Ok ()) := by
  sorry

/-- conditional: an input of more than 32768 bytes (32769 is the smallest) is rejected with an
error whose root cause is the keystore2 error `Rc(TOO_MUCH_DATA)`, with no context.
Hypotheses: the external constant `ResponseCode::TOO_MUCH_DATA` is `rc`; the assumptions about
`anyhow::kind::Trait::new` (`AnyhowKindTraitNewSpec`) and `anyhow::__private::must_use`
(`AnyhowMustUseSpec`). -/
theorem check_input_length_too_long (root : anyhow.Error → ErrRoot)
    (hnew : AnyhowKindTraitNewSpec root) (hmust : AnyhowMustUseSpec)
    (rc : ResponseCode.ResponseCode)
    (hrc : ResponseCode.ResponseCode.TOO_MUCH_DATA = ok rc)
    (data : Slice Std.U8) (h : 32768 < data.length) :
    ∃ e, checkInputLength data = ok (.Err e) ∧ root e = ErrRoot.ks (error.Error.Rc rc) := by
  sorry
