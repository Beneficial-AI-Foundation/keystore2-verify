import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.ffi.c_str (CString)
open core.ffi.c_str (CStr)
open alloc.ffi.c_str.CString.Insts renaming CoreOpsDerefDerefCStr → cstringDeref

/-- conditional: when `anyhow_error_to_cstring` gives no message, `into_binder` returns the
status that `Status::new_service_specific_error` makes from the serialized code of `e` and no
message. The serializer `anyhow_error_to_serialized_error` is not translated, so its result is
a hypothesis. Hypotheses: it returns `ok rc`; `anyhow_error_to_cstring` returns `ok none`; the
assumption about `Option::as_deref`. -/
theorem into_binder_no_message (e : anyhow.Error) (rc : error.SerializedError)
    (hrc : error.anyhow_error_to_serialized_error e = ok rc)
    (hmsg : error.anyhow_error_to_cstring e = ok none)
    (hder : CStringAsDerefSpec) :
    error.into_binder e = binder.Status.new_service_specific_error rc none := by
  sorry

/-- conditional: when `anyhow_error_to_cstring` gives the message `msg`, `into_binder` returns
the status that `Status::new_service_specific_error` makes from the serialized code of `e` and
the borrowed message. Hypotheses: the serializer returns `ok rc`; `anyhow_error_to_cstring`
returns `ok (some msg)`; `deref` of `msg` returns `ok m`; the assumption about
`Option::as_deref`. -/
theorem into_binder_message (e : anyhow.Error) (rc : error.SerializedError)
    (msg : CString) (m : CStr)
    (hrc : error.anyhow_error_to_serialized_error e = ok rc)
    (hmsg : error.anyhow_error_to_cstring e = ok (some msg))
    (hd : cstringDeref.deref msg = ok m)
    (hder : CStringAsDerefSpec) :
    error.into_binder e = binder.Status.new_service_specific_error rc (some m) := by
  sorry

end Keystore2Verify.Error
