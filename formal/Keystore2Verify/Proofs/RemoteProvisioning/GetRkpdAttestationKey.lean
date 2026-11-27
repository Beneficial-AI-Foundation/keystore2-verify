import Keystore2Verify.Specs.Defs.RemoteProvisioning

namespace Keystore2Verify.RemoteProvisioning
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open remote_provisioning renaming get_rkpd_attestation_key → getRkpdKey
open android_security_rkp_aidl.aidl.android.security.rkp.RemotelyProvisionedKey
  renaming RemotelyProvisionedKey → RemotelyProvisionedKey

/-- conditional: if the name of the remotely provisioned component of `security_level` is
`nm`, `get_rkpd_attestation_key` returns `Ok v` when `rkpd_client::get_rkpd_attestation_key`
returns `Ok v` for the name and for `caller_uid` converted to a `u32` (`as u32`, which wraps).
Nothing is added to the result. The watchdog call is a no-op in the build without the
`watchdog` feature.
Hypotheses: the name lookup returns `Ok nm`; the outcomes of `String::deref` and of
`rkpd_client::get_rkpd_attestation_key` (a binder call); `format` and `from_str_nonconst` do not
fail; the assumption about `context` for an `anyhow::Error` (`AnyCtxLaw`). -/
theorem get_rkpd_attestation_key_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root String)
    (security_level : SecurityLevel.SecurityLevel) (caller_uid : utils.AppUid)
    (nm : String)
    (hname : globals.get_remotely_provisioned_component_name security_level = ok (.Ok nm))
    (s : Str) (hderef : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref nm = ok s)
    (v : RemotelyProvisionedKey)
    (hrkpd : rkpd_client.get_rkpd_attestation_key s (IScalar.hcast .U32 caller_uid) =
      ok (.Ok v)) :
    getRkpdKey security_level caller_uid = ok (.Ok v) := by
  sorry

/-- conditional: if the lookup and the call that the function forwards to have the outcomes
below and the final result is an error `e`, the function returns an error with the same root
cause (nothing is added). Hypotheses: the name lookup returns `Ok nm`; the outcomes of
`String::deref` and of `rkpd_client::get_rkpd_attestation_key` (a binder call); `format` and
`from_str_nonconst` do not fail; the assumption about `context` for an `anyhow::Error`
(`AnyCtxLaw`). -/
theorem get_rkpd_attestation_key_downstream_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root String)
    (security_level : SecurityLevel.SecurityLevel) (caller_uid : utils.AppUid)
    (nm : String)
    (hname : globals.get_remotely_provisioned_component_name security_level = ok (.Ok nm))
    (s : Str) (hderef : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref nm = ok s)
    (e : anyhow.Error)
    (hrkpd : rkpd_client.get_rkpd_attestation_key s (IScalar.hcast .U32 caller_uid) =
      ok (.Err e)) :
    ∃ e', getRkpdKey security_level caller_uid = ok (.Err e') ∧ root e' = root e := by
  sorry

/-- conditional: if the name lookup returns an error `e`, `get_rkpd_attestation_key` returns an
error with the same root cause. In the Rust source this path returns before
`rkpd_client::get_rkpd_attestation_key` is called. Hypotheses: the name lookup returns `Err e`;
`format` and `from_str_nonconst` do not fail; the assumption about `context` for an `anyhow::Error`
(`AnyCtxLaw`). -/
theorem get_rkpd_attestation_key_name_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root String)
    (security_level : SecurityLevel.SecurityLevel) (caller_uid : utils.AppUid)
    (e : anyhow.Error)
    (hname : globals.get_remotely_provisioned_component_name security_level = ok (.Err e)) :
    ∃ e', getRkpdKey security_level caller_uid = ok (.Err e') ∧ root e' = root e := by
  sorry
