import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open android_security_apc.aidl.android.security.apc
open ResponseCode.ResponseCode renaming OK → apcOk, CANCELLED → apcCancelled,
  ABORTED → apcAborted, OPERATION_PENDING → apcOperationPending, IGNORED → apcIgnored,
  SYSTEM_ERROR → apcSystemError

/-- conditional: for the code `0`, `compat_2_response_code` returns the constant
`ResponseCode::OK` of the APC interface. Hypothesis: the constant is `ok c` (`hc`). -/
theorem compat_2_response_code_ok (c : ResponseCode.ResponseCode)
    (hc : apcOk = ok c) : utils.compat_2_response_code 0#u32 = ok c := by
  sorry

/-- conditional: for the code `1`, `compat_2_response_code` returns the constant
`ResponseCode::CANCELLED` of the APC interface. Hypothesis: the constant is `ok c` (`hc`). -/
theorem compat_2_response_code_cancelled (c : ResponseCode.ResponseCode)
    (hc : apcCancelled = ok c) : utils.compat_2_response_code 1#u32 = ok c := by
  sorry

/-- conditional: for the code `2`, `compat_2_response_code` returns the constant
`ResponseCode::ABORTED` of the APC interface. Hypothesis: the constant is `ok c` (`hc`). -/
theorem compat_2_response_code_aborted (c : ResponseCode.ResponseCode)
    (hc : apcAborted = ok c) : utils.compat_2_response_code 2#u32 = ok c := by
  sorry

/-- conditional: for the code `3`, `compat_2_response_code` returns the constant
`ResponseCode::OPERATION_PENDING` of the APC interface. Hypothesis: the constant is `ok c`
(`hc`). -/
theorem compat_2_response_code_operation_pending (c : ResponseCode.ResponseCode)
    (hc : apcOperationPending = ok c) : utils.compat_2_response_code 3#u32 = ok c := by
  sorry

/-- conditional: for the code `4`, `compat_2_response_code` returns the constant
`ResponseCode::IGNORED` of the APC interface. Hypothesis: the constant is `ok c` (`hc`). -/
theorem compat_2_response_code_ignored (c : ResponseCode.ResponseCode)
    (hc : apcIgnored = ok c) : utils.compat_2_response_code 4#u32 = ok c := by
  sorry

/-- conditional: for the code `5`, `compat_2_response_code` returns the constant
`ResponseCode::SYSTEM_ERROR` of the APC interface. Hypothesis: the constant is `ok c` (`hc`). -/
theorem compat_2_response_code_system_error (c : ResponseCode.ResponseCode)
    (hc : apcSystemError = ok c) : utils.compat_2_response_code 5#u32 = ok c := by
  sorry

/-- conditional: for every code `rc` of 6 or more, `compat_2_response_code` returns the constant
`ResponseCode::SYSTEM_ERROR`, as for the code 5. Hypothesis: the constant is `ok c` (`hc`). -/
theorem compat_2_response_code_other (c : ResponseCode.ResponseCode) (rc : Std.U32)
    (hrc : 6 ≤ rc.val) (hc : apcSystemError = ok c) :
    utils.compat_2_response_code rc = ok c := by
  sorry

end Keystore2Verify.Utils
