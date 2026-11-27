import Keystore2Verify.Specs.Defs.Globals

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open alloc.string.String.Insts
open android_hardware_security_keymint.aidl.android.hardware.security.keymint

/-! In `get_remotely_provisioned_component_name`, the instance name is the descriptor, then
`/default` for the level 1 (`TRUSTED_ENVIRONMENT`) or `/strongbox` for the level 2 (`STRONGBOX`).
The model of formatting does not carry the text (see `Externals`): `s` below is the string that
`format!` returns, and `s1` is its view as a `str`. In the translation the argument of `format` is
the unit value, so both arms use the same `format` result. For the same reason the hypothesis on
`format` also covers the `format!` that builds the context text on the paths where `is_declared`
returns `Ok`. In the Rust source that is a second call with another result; the statements need of
it only the idealisation that formatting never panics. The errors are stated by their root cause:
the context text of the Rust source is `keystore2/src/globals.rs:451: Failed to get rpc for sec
level ` and the `Debug` text of the level. -/

/-- conditional: if the level is 1 or 2, `format!` returns `s`, `s` has the view `s1`, and
`is_declared(s1)` returns `Ok(true)`, the function returns `Ok(s)`: the instance name. Hypotheses:
the outcome of `format` (also used for the context text, see above), of the view, of `is_declared`
and of the constant `ErrorCode::HARDWARE_TYPE_UNAVAILABLE` (`ec`), and the assumption for
`Result::context` at the call that adds the context to `Ok`. -/
theorem get_remotely_provisioned_component_name_declared (root : anyhow.Error → ErrRoot)
    (hctx : KsCtxSpec root String) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.HARDWARE_TYPE_UNAVAILABLE = ok ec)
    (sl : SecLevel) (hsl : sl = 1#i32 ∨ sl = 2#i32) (s : String) (s1 : Str)
    (hfmt : alloc.fmt.format () = ok s)
    (hview : CoreOpsDerefDerefStr.deref s = ok s1)
    (hdecl : binder.is_declared s1 = ok (.Ok true)) :
    globals.get_remotely_provisioned_component_name sl = ok (.Ok s) := by
  sorry

/-- conditional: if the level is 1 or 2, `format!` returns `s`, `s` has the view `s1`, and
`is_declared(s1)` returns `Ok(false)`, the function returns an error whose root cause is
`Error::Km(ec)`, where `ec` is `ErrorCode::HARDWARE_TYPE_UNAVAILABLE`. Hypotheses: the
outcome of `format` (also used for the context text, see above), of the view, of
`is_declared` and of the constant, and the assumption for
`Result::context` at the call that adds the context to an `Err`. -/
theorem get_remotely_provisioned_component_name_undeclared (root : anyhow.Error → ErrRoot)
    (hctx : KsCtxSpec root String) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.HARDWARE_TYPE_UNAVAILABLE = ok ec)
    (sl : SecLevel) (hsl : sl = 1#i32 ∨ sl = 2#i32) (s : String) (s1 : Str)
    (hfmt : alloc.fmt.format () = ok s)
    (hview : CoreOpsDerefDerefStr.deref s = ok s1)
    (hdecl : binder.is_declared s1 = ok (.Ok false)) :
    ∃ e, globals.get_remotely_provisioned_component_name sl = ok (.Err e) ∧
      KmRoot root ec e := by
  sorry

/-- conditional: if the level is neither 1 nor 2 (it can be 0, 100 or any other number), the
function returns an error whose root cause is `Error::Km(ec)`, where `ec` is
`ErrorCode::HARDWARE_TYPE_UNAVAILABLE`. In the Rust source this path returns before `is_declared` is
called. Hypotheses: the assumption for `format`, the outcome of the constant, and the assumption
about `Result::context` at the call that adds the context to an `Err`. -/
theorem get_remotely_provisioned_component_name_other_level (root : anyhow.Error → ErrRoot)
    (hctx : KsCtxSpec root String) (hfmt : AllocFmtFormatSpec) (ec : ErrorCode.ErrorCode)
    (hec : ErrorCode.ErrorCode.HARDWARE_TYPE_UNAVAILABLE = ok ec)
    (sl : SecLevel) (h1 : sl ≠ 1#i32) (h2 : sl ≠ 2#i32) :
    ∃ e, globals.get_remotely_provisioned_component_name sl = ok (.Err e) ∧
      KmRoot root ec e := by
  sorry

/-- conditional: if the level is 1 or 2, `format!` returns `s`, `s` has the view `s1`, and
`is_declared(s1)` returns the status code `Err(st)`, the function returns at once an error made
from `st`. No `HARDWARE_TYPE_UNAVAILABLE` and no context are added; the root cause is not a class
that the model knows. Hypotheses: the outcomes of `format`, of the view and of `is_declared`, and
the assumption for `anyhow::Error::from` at a status code. -/
theorem get_remotely_provisioned_component_name_status_error (root : anyhow.Error → ErrRoot)
    (hfrom : StatusCodeFromSpec root)
    (sl : SecLevel) (hsl : sl = 1#i32 ∨ sl = 2#i32) (s : String) (s1 : Str)
    (st : binder.StatusCode)
    (hfmt : alloc.fmt.format () = ok s)
    (hview : CoreOpsDerefDerefStr.deref s = ok s1)
    (hdecl : binder.is_declared s1 = ok (.Err st)) :
    ∃ e, globals.get_remotely_provisioned_component_name sl = ok (.Err e) ∧
      root e = ErrRoot.other := by
  sorry

end Keystore2Verify.Globals
