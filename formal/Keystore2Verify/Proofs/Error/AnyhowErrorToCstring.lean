import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open alloc.ffi.c_str (CString NulError)
open alloc.ffi.c_str.CString renaming new → cstringNew
open alloc.vec.VecU8.Insts renaming CoreConvertFromString → vecFromString
open Aeneas.Std.core.result.Result renaming Ok → rOk, Err → rErr

/-- conditional: if `CString::new` accepts the formatted text, `anyhow_error_to_cstring` returns
`Some msg` with the string it made. Hypotheses: `format` returns `ok s` and `CString::new`
returns `Ok msg` on `s`. The formatting arguments are erased in the translation, so the call
`format ()` stands for the text of the `anyhow::Error`. -/
theorem anyhow_error_to_cstring_ok (e : anyhow.Error) (s : String)
    (msg : CString)
    (hfmt : alloc.fmt.format () = ok s)
    (hnew : cstringNew (core.convert.IntoFrom vecFromString) s = ok (rOk msg)) :
    error.anyhow_error_to_cstring e = ok (some msg) := by
  sorry

/-- conditional: if `CString::new` rejects the formatted text, `anyhow_error_to_cstring` returns
`None`. In the Rust source this path also logs a warning. Hypotheses: `format` returns `ok s`,
`CString::new` returns `Err n` on `s`, and the four assumptions about logging. -/
theorem anyhow_error_to_cstring_err (e : anyhow.Error) (s : String)
    (n : NulError)
    (hfmt : alloc.fmt.format () = ok s)
    (hnew : cstringNew (core.convert.IntoFrom vecFromString) s = ok (rErr n))
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) :
    error.anyhow_error_to_cstring e = ok none := by
  sorry

end Keystore2Verify.Error
