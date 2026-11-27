import Keystore2Verify.Proofs.RemoteProvisioning.RemProvState
import Keystore2Verify.Proofs.RemoteProvisioning.IsRkpOnly
import Keystore2Verify.Proofs.RemoteProvisioning.IsRkpEnabled
import Keystore2Verify.Proofs.RemoteProvisioning.IsAsymmetricKey
import Keystore2Verify.Proofs.RemoteProvisioning.GetRkpdAttestationKey

namespace Keystore2Verify.RemoteProvisioning

section RemProvState
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open remote_provisioning.RemProvState.Insts.CoreDefaultDefault renaming default → provDefault
open remote_provisioning.RemProvState renaming new → provNew
open SecurityLevel.SecurityLevel.Insts.CoreDefaultDefault renaming default → levelDefault

recall rem_prov_state_default (sl : SecurityLevel.SecurityLevel) (h : levelDefault = ok sl) :
    provDefault = ok { security_level := sl }

recall rem_prov_state_new (security_level : SecurityLevel.SecurityLevel) :
    provNew security_level = ok { security_level := security_level }

end RemProvState

section IsRkpOnly
open Aeneas Aeneas.Std Result keystore2
open remote_provisioning.RemProvState renaming is_rkp_only → isRkpOnly
open rustutils.android.system_properties

recall is_rkp_only_strongbox (self : remote_provisioning.RemProvState)
    (hl : self.security_level = 2#i32)
    (r : core.result.Result Bool PropertyWatcherError)
    (h : read_bool (toStr "remote_provisioning.strongbox.rkp_only") false = ok r) :
    isRkpOnly self = ok (propBool r)

recall is_rkp_only_tee (self : remote_provisioning.RemProvState)
    (hl : self.security_level = 1#i32)
    (r : core.result.Result Bool PropertyWatcherError)
    (h : read_bool (toStr "remote_provisioning.tee.rkp_only") false = ok r) :
    isRkpOnly self = ok (propBool r)

recall is_rkp_only_other (self : remote_provisioning.RemProvState)
    (h1 : self.security_level ≠ 1#i32) (h2 : self.security_level ≠ 2#i32) :
    isRkpOnly self = ok false

end IsRkpOnly

section IsRkpEnabled
open Aeneas Aeneas.Std Result keystore2
open remote_provisioning.RemProvState renaming is_rkp_enabled → isRkpEnabled
open rustutils.android.system_properties

recall is_rkp_enabled_some (self : remote_provisioning.RemProvState)
    (value : String) (b : Bool)
    (hread : read (toStr "remote_provisioning.hostname") =
      ok (core.result.Result.Ok (some value) : core.result.Result _ PropertyWatcherError))
    (hempty : alloc.string.String.is_empty value = ok b) :
    isRkpEnabled self = ok (!b)

recall is_rkp_enabled_none (self : remote_provisioning.RemProvState)
    (r : core.result.Result (Option String) PropertyWatcherError)
    (hread : read (toStr "remote_provisioning.hostname") = ok r)
    (hnone : r = .Ok none ∨ ∃ e, r = .Err e) :
    isRkpEnabled self = ok false

end IsRkpEnabled

section IsAsymmetricKey
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open remote_provisioning.RemProvState renaming is_asymmetric_key → isAsymmetricKey
open remote_provisioning.RemProvState.is_asymmetric_key.closure.Insts
  renaming CoreOpsFunctionFnMutTupleShared0KeyParameterBool → asymClosure

recall is_asymmetric_key_iff (hany : CoreSliceIterAnySpec asymClosure)
    (self : remote_provisioning.RemProvState) (params : Slice KeyParameter.KeyParameter) :
    ∃ b, isAsymmetricKey self params = ok b ∧
      (b = true ↔ ∃ p ∈ params.val, IsAsymParam p)

end IsAsymmetricKey

section GetRkpdAttestationKey
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open remote_provisioning renaming get_rkpd_attestation_key → getRkpdKey
open android_security_rkp_aidl.aidl.android.security.rkp.RemotelyProvisionedKey
  renaming RemotelyProvisionedKey → RemotelyProvisionedKey

recall get_rkpd_attestation_key_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root String)
    (security_level : SecurityLevel.SecurityLevel) (caller_uid : utils.AppUid)
    (nm : String)
    (hname : globals.get_remotely_provisioned_component_name security_level = ok (.Ok nm))
    (s : Str) (hderef : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref nm = ok s)
    (v : RemotelyProvisionedKey)
    (hrkpd : rkpd_client.get_rkpd_attestation_key s (IScalar.hcast .U32 caller_uid) =
      ok (.Ok v)) :
    getRkpdKey security_level caller_uid = ok (.Ok v)

recall get_rkpd_attestation_key_downstream_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root String)
    (security_level : SecurityLevel.SecurityLevel) (caller_uid : utils.AppUid)
    (nm : String)
    (hname : globals.get_remotely_provisioned_component_name security_level = ok (.Ok nm))
    (s : Str) (hderef : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref nm = ok s)
    (e : anyhow.Error)
    (hrkpd : rkpd_client.get_rkpd_attestation_key s (IScalar.hcast .U32 caller_uid) =
      ok (.Err e)) :
    ∃ e', getRkpdKey security_level caller_uid = ok (.Err e') ∧ root e' = root e

recall get_rkpd_attestation_key_name_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root String)
    (security_level : SecurityLevel.SecurityLevel) (caller_uid : utils.AppUid)
    (e : anyhow.Error)
    (hname : globals.get_remotely_provisioned_component_name security_level = ok (.Err e)) :
    ∃ e', getRkpdKey security_level caller_uid = ok (.Err e') ∧ root e' = root e

end GetRkpdAttestationKey

end Keystore2Verify.RemoteProvisioning
