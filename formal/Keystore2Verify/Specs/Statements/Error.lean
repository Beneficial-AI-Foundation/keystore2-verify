import Keystore2Verify.Proofs.Error.Error
import Keystore2Verify.Proofs.Error.Sys
import Keystore2Verify.Proofs.Error.Perm
import Keystore2Verify.Proofs.Error.LogLevel
import Keystore2Verify.Proofs.Error.FromRkpdError
import Keystore2Verify.Proofs.Error.FromPostProcessorError
import Keystore2Verify.Proofs.Error.MapBinderStatusCode
import Keystore2Verify.Proofs.Error.LogClientError
import Keystore2Verify.Proofs.Error.AnyhowErrorToCstring
import Keystore2Verify.Proofs.Error.IntoBinder
import Keystore2Verify.Proofs.Error.SerializedError
import Keystore2Verify.Proofs.Error.ErrorToSerializedError

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

section Error
open error.Error.Insts.CoreCmpPartialEqError renaming eq → errorEq
open error.Error.BinderTransaction renaming constructor → binderTransactionNew

recall Error_eq_different_variants (x y : error.Error)
    (h : error.Error.read_discriminant x ≠ error.Error.read_discriminant y) :
    errorEq x y = ok false

recall Error_eq_rc (a b : Std.I32)
    (hrc : ResponseCodeEqSpec) :
    ∃ r, errorEq (error.Error.Rc a) (error.Error.Rc b) = ok r ∧ (r = true ↔ a = b)

recall Error_eq_km (a b : Std.I32)
    (hec : ErrorCodeEqSpec) :
    ∃ r, errorEq (error.Error.Km a) (error.Error.Km b) = ok r ∧ (r = true ↔ a = b)

recall Error_eq_binder_number_differs (c c' : binder.ExceptionCode) (n n' : Std.I32)
    (h : n ≠ n') :
    errorEq (error.Error.Binder c n) (error.Error.Binder c' n') = ok false

recall Error_eq_binder_same_number (c c' : binder.ExceptionCode) (n : Std.I32)
    (hex : ExceptionCodeEqSpec) :
    ∃ r, errorEq (error.Error.Binder c n) (error.Error.Binder c' n) = ok r ∧
      (r = true ↔ c = c')

recall Error_eq_binder_transaction (s s' : binder.StatusCode) (hsc : StatusCodeEqSpec) :
    ∃ r, errorEq (error.Error.BinderTransaction s) (error.Error.BinderTransaction s') = ok r ∧
      (r = true ↔ s = s')

recall Error_BinderTransaction_constructor (s : binder.StatusCode) :
    binderTransactionNew s = ok (error.Error.BinderTransaction s)

end Error

section Sys

recall Error_sys : error.Error.sys = ok (error.Error.Rc 4#i32)

end Sys

section Perm
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode

recall Error_perm (c : Std.I32) (hc : ResponseCode.PERMISSION_DENIED = ok c) :
    error.Error.perm = ok (error.Error.Rc c)

end Perm

section LogLevel

recall Error_log_level_rc (c : Std.I32) :
    error.Error.log_level (error.Error.Rc c) =
      ok (if c = 7#i32 then none else some log.Level.Error)

recall Error_log_level_km (c : Std.I32) :
    error.Error.log_level (error.Error.Km c) =
      ok (if c = (-26)#i32 ∨ c = (-67)#i32 then some log.Level.Info
        else some log.Level.Error)

recall Error_log_level_binder (c : binder.ExceptionCode) (n : Std.I32) :
    error.Error.log_level (error.Error.Binder c n) = ok (some log.Level.Error)

recall Error_log_level_binder_transaction (s : binder.StatusCode) :
    error.Error.log_level (error.Error.BinderTransaction s) = ok (some log.Level.Error)

end LogLevel

section FromRkpdError
open error.Error.Insts.CoreConvertFromError renaming «from» → errorFromRkpd
open android_system_keystore2.aidl.android.system.keystore2.ResponseCode

recall Error_from_rkpd_transient (e : rkpd_client.Error) (c : Std.I32)
    (he : e = rkpd_client.Error.RequestCancelled ∨ e = rkpd_client.Error.GetRegistrationFailed ∨
      e = rkpd_client.Error.RetryableTimeout)
    (hc : ResponseCode.OUT_OF_KEYS_TRANSIENT_ERROR = ok c) :
    errorFromRkpd e = ok (error.Error.Rc c)

recall Error_from_rkpd_get_key_unknown (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_TRANSIENT_ERROR = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 1#i8) = ok (error.Error.Rc c)

recall Error_from_rkpd_get_key_permanent (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_PERMANENT_ERROR = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 5#i8) = ok (error.Error.Rc c)

recall Error_from_rkpd_get_key_pending (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_PENDING_INTERNET_CONNECTIVITY = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 3#i8) = ok (error.Error.Rc c)

recall Error_from_rkpd_get_key_security_patch (c : Std.I32)
    (hc : ResponseCode.OUT_OF_KEYS_REQUIRES_SYSTEM_UPGRADE = ok c) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed 2#i8) = ok (error.Error.Rc c)

recall Error_from_rkpd_get_key_other (g : Std.I8) (c : Std.I32)
    (h1 : g ≠ 1#i8) (h2 : g ≠ 2#i8) (h3 : g ≠ 3#i8) (h5 : g ≠ 5#i8)
    (hc : ResponseCode.OUT_OF_KEYS_TRANSIENT_ERROR = ok c)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) :
    errorFromRkpd (rkpd_client.Error.GetKeyFailed g) = ok (error.Error.Rc c)

recall Error_from_rkpd_system_error (e : rkpd_client.Error)
    (he : e = rkpd_client.Error.StoreUpgradedKeyFailed ∨ e = rkpd_client.Error.Timeout) :
    errorFromRkpd e = ok (error.Error.Rc 4#i32)

recall Error_from_rkpd_binder_transaction (s : binder.StatusCode) :
    errorFromRkpd (rkpd_client.Error.BinderTransaction s) =
      ok (error.Error.BinderTransaction s)

recall Error_from_rkpd_too_many_operations (c : Std.I32)
    (hc : ResponseCode.BACKEND_BUSY = ok c) :
    errorFromRkpd rkpd_client.Error.TooManyConcurrentOperations = ok (error.Error.Rc c)

end FromRkpdError

section FromPostProcessorError
open error.Error.Insts.CoreConvertFromPostProcessorError
  renaming «from» → errorFromPostProcessor

recall Error_from_post_processor (s : postprocessor_client.PostProcessorError) :
    errorFromPostProcessor s = ok (error.Error.BinderTransaction s)

end FromPostProcessorError

section MapBinderStatusCode
open Aeneas.Std.core.result.Result renaming Ok → rOk, Err → rErr

recall map_binder_status_code_ok {T : Type} (t : T) :
    error.map_binder_status_code
      (rOk t : core.result.Result T binder.StatusCode) =
      ok (rOk t)

recall map_binder_status_code_err {T : Type} (s : binder.StatusCode) :
    error.map_binder_status_code
      (rErr s : core.result.Result T binder.StatusCode) =
      ok (rErr (error.Error.BinderTransaction s))

end MapBinderStatusCode

section LogClientError

recall log_client_error_none (e : anyhow.Error) :
    error.log_client_error none e = ok ()

recall log_client_error_some (l : log.Level) (e : anyhow.Error) (u : Std.U32)
    (huid : binder.ThreadState.get_calling_uid = ok u)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) :
    error.log_client_error (some l) e = ok ()

end LogClientError

section AnyhowErrorToCstring
open alloc.ffi.c_str (CString NulError)
open alloc.ffi.c_str.CString renaming new → cstringNew
open alloc.vec.VecU8.Insts renaming CoreConvertFromString → vecFromString
open Aeneas.Std.core.result.Result renaming Ok → rOk, Err → rErr

recall anyhow_error_to_cstring_ok (e : anyhow.Error) (s : String)
    (msg : CString)
    (hfmt : alloc.fmt.format () = ok s)
    (hnew : cstringNew (core.convert.IntoFrom vecFromString) s = ok (rOk msg)) :
    error.anyhow_error_to_cstring e = ok (some msg)

recall anyhow_error_to_cstring_err (e : anyhow.Error) (s : String)
    (n : NulError)
    (hfmt : alloc.fmt.format () = ok s)
    (hnew : cstringNew (core.convert.IntoFrom vecFromString) s = ok (rErr n))
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) :
    error.anyhow_error_to_cstring e = ok none

end AnyhowErrorToCstring

section IntoBinder
open alloc.ffi.c_str (CString)
open core.ffi.c_str (CStr)
open alloc.ffi.c_str.CString.Insts renaming CoreOpsDerefDerefCStr → cstringDeref

recall into_binder_no_message (e : anyhow.Error) (rc : error.SerializedError)
    (hrc : error.anyhow_error_to_serialized_error e = ok rc)
    (hmsg : error.anyhow_error_to_cstring e = ok none)
    (hder : CStringAsDerefSpec) :
    error.into_binder e = binder.Status.new_service_specific_error rc none

recall into_binder_message (e : anyhow.Error) (rc : error.SerializedError)
    (msg : CString) (m : CStr)
    (hrc : error.anyhow_error_to_serialized_error e = ok rc)
    (hmsg : error.anyhow_error_to_cstring e = ok (some msg))
    (hd : cstringDeref.deref msg = ok m)
    (hder : CStringAsDerefSpec) :
    error.into_binder e = binder.Status.new_service_specific_error rc (some m)

end IntoBinder

section SerializedError
open error.SerializedError.Insts
open CoreCloneClone renaming clone → serializedClone
open CoreCmpPartialEqSerializedError renaming eq → serializedEq
open CoreCmpOrd renaming cmp → serializedCmp
open CoreCmpPartialOrdSerializedError renaming partial_cmp → serializedPartialCmp

recall SerializedError_clone (x : error.SerializedError) : serializedClone x = ok x

recall SerializedError_eq (x y : error.SerializedError) :
    serializedEq x y = ok (decide (x = y))

recall SerializedError_cmp (x y : error.SerializedError) :
    serializedCmp x y = ok (compare x.val y.val)

recall SerializedError_partial_cmp (x y : error.SerializedError) :
    serializedPartialCmp x y = ok (some (compare x.val y.val))

end SerializedError

section ErrorToSerializedError

recall error_to_serialized_error_rc (c : Std.I32) :
    error.error_to_serialized_error (error.Error.Rc c) = ok c

recall error_to_serialized_error_km (c : Std.I32) :
    error.error_to_serialized_error (error.Error.Km c) = ok c

recall error_to_serialized_error_binder (c : binder.ExceptionCode) (n : Std.I32) :
    error.error_to_serialized_error (error.Error.Binder c n) = ok 4#i32

recall error_to_serialized_error_binder_transaction (s : binder.StatusCode) :
    error.error_to_serialized_error (error.Error.BinderTransaction s) = ok 4#i32

end ErrorToSerializedError

end Keystore2Verify.Error
