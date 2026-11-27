import Keystore2Verify.Specs.Defs.KmCompat

namespace Keystore2Verify.KmCompat
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2.core.slice.Slice renaming starts_with → sliceStartsWith
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming eq → sliceVecEq
open km_compat renaming wrap_keyblob → wrapKeyblob, unwrap_keyblob → unwrapKeyblob

/-- exact: the import format `PKCS8` (the number 1) gives `Ok (Pkcs8 key_data)`; the data slice is
stored unchanged. -/
theorem key_import_data_new_pkcs8 (key_data : Slice Std.U8) :
    km_compat.KeyImportData.new 1#i32 key_data = ok (.Ok (.Pkcs8 key_data)) := by
  sorry

/-- exact: the import format `RAW` (the number 3) gives `Ok (Raw key_data)`; the data slice is
stored unchanged. -/
theorem key_import_data_new_raw (key_data : Slice Std.U8) :
    km_compat.KeyImportData.new 3#i32 key_data = ok (.Ok (.Raw key_data)) := by
  sorry

/-- conditional: any other import format gives `Err s`, where `s` is the binder status that
`new_service_specific_error` makes from the code `UNSUPPORTED_KEY_FORMAT` and no message.
Hypotheses: the format is neither 1 nor 3, the value `ec` of the constant
`UNSUPPORTED_KEY_FORMAT`, and the outcome of `new_service_specific_error` on `ec` and no
message. -/
theorem key_import_data_new_err (key_format : Std.I32) (key_data : Slice Std.U8)
    (ec : Std.I32) (s : binder.Status)
    (h1 : key_format ≠ 1#i32) (h3 : key_format ≠ 3#i32)
    (hec : ErrorCode.ErrorCode.UNSUPPORTED_KEY_FORMAT = ok ec)
    (hs : binder.Status.new_service_specific_error ec none = ok s) :
    km_compat.KeyImportData.new key_format key_data = ok (.Err s) := by
  sorry

end Keystore2Verify.KmCompat
