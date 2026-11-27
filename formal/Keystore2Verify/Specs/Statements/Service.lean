import Keystore2Verify.Proofs.Service.ListEntries
import Keystore2Verify.Proofs.Service.CountNumEntries
import Keystore2Verify.Proofs.Service.GetSupplementaryAttestationInfo

namespace Keystore2Verify.Service

section ListEntries
open Aeneas Aeneas.Std Result keystore2
open std.thread.local.LocalKey renaming «with» → localLocalKeywith
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open service.KeystoreService
open service.KeystoreService.list_entries.closure.Insts
  renaming
    CoreOpsFunctionFnOnceTupleShared2RefCellKeystoreDBResultVecKeyDescriptorError → listClosure
open service.KeystoreService.list_entries_batched.closure.Insts
  renaming
    CoreOpsFunctionFnOnceTupleShared4RefCellKeystoreDBResultVecKeyDescriptorError → batchClosure

recall list_entries_ok (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (v : (alloc.vec.Vec KeyDescriptor.KeyDescriptor))
    (hwith : localLocalKeywith listClosure lk (k.domain, k.nspace) = ok (.Ok v)) :
    list_entries self domain ns = ok (.Ok v)

recall list_entries_downstream_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (e : anyhow.Error)
    (hwith : localLocalKeywith listClosure lk (k.domain, k.nspace) = ok (.Err e)) :
    ∃ e', list_entries self domain ns = ok (.Err e') ∧ root e' = root e

recall list_entries_lookup_err (root : anyhow.Error → ErrRoot) (self : service.KeystoreService)
    (domain : Domain.Domain) (ns : Std.I64) (e : anyhow.Error)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Err e)) :
    ∃ e', list_entries self domain ns = ok (.Err e') ∧ root e' = root e

recall list_entries_batched_ok (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (start_past_alias : Option Str) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (v : (alloc.vec.Vec KeyDescriptor.KeyDescriptor))
    (hwith : localLocalKeywith batchClosure lk
      (k.domain, k.nspace, start_past_alias) = ok (.Ok v)) :
    list_entries_batched self domain ns start_past_alias = ok (.Ok v)

recall list_entries_batched_downstream_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (start_past_alias : Option Str) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk)
    (e : anyhow.Error)
    (hwith : localLocalKeywith batchClosure lk
      (k.domain, k.nspace, start_past_alias) = ok (.Err e)) :
    ∃ e', list_entries_batched self domain ns start_past_alias = ok (.Err e') ∧
      root e' = root e

recall list_entries_batched_lookup_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain) (ns : Std.I64)
    (start_past_alias : Option Str) (e : anyhow.Error)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Err e)) :
    ∃ e', list_entries_batched self domain ns start_past_alias = ok (.Err e') ∧
      root e' = root e

end ListEntries

section CountNumEntries
open Aeneas Aeneas.Std Result keystore2
open std.thread.local.LocalKey renaming «with» → localLocalKeywith
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open service.KeystoreService
open service.KeystoreService.count_num_entries.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleShared2RefCellKeystoreDBResultI32Error → countClosure

recall count_num_entries_ok (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (v : Std.I32)
    (hwith : localLocalKeywith countClosure lk (k.domain, k.nspace) = ok (.Ok v)) :
    count_num_entries self domain ns = ok (.Ok v)

recall count_num_entries_downstream_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain)
    (ns : Std.I64) (k : KeyDescriptor.KeyDescriptor)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Ok k))
    (lk : std.thread.local.LocalKey (core.cell.RefCell database.KeystoreDB))
    (hdb : globals.DB = ok lk) (e : anyhow.Error)
    (hwith : localLocalKeywith countClosure lk (k.domain, k.nspace) = ok (.Err e)) :
    ∃ e', count_num_entries self domain ns = ok (.Err e') ∧ root e' = root e

recall count_num_entries_lookup_err (root : anyhow.Error → ErrRoot)
    (self : service.KeystoreService) (domain : Domain.Domain) (ns : Std.I64) (e : anyhow.Error)
    (hlook : get_key_descriptor_for_lookup self domain ns = ok (.Err e)) :
    ∃ e', count_num_entries self domain ns = ok (.Err e') ∧ root e' = root e

end CountNumEntries

section GetSupplementaryAttestationInfo
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals Keystore2Verify.AttestationKeyUtils
open Keystore2Verify.Permission (invalidArgumentError)
open android_system_keystore2.aidl.android.system.keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open service.KeystoreService renaming get_supplementary_attestation_info → getSupp
open std.sync.poison.rwlock

recall get_supplementary_attestation_info_other (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8))
    (self : service.KeystoreService) (tag : Tag.Tag) (h : tag ≠ (-1879047468)#i32) :
    ∃ e, getSupp self tag = ok (.Err e) ∧ root e = ErrRoot.ks invalidArgumentError

recall get_supplementary_attestation_info_poisoned (self : service.KeystoreService)
    (rl : RwLock (Option (alloc.vec.Vec Std.U8))) (hrl : globals.ENCODED_MODULE_INFO = ok rl)
    (pe : std.sync.poison.PoisonError (RwLockReadGuard (Option (alloc.vec.Vec Std.U8))))
    (hread : RwLock.read rl = ok (.Err pe)) :
    getSupp self (-1879047468)#i32 = fail Error.panic

recall get_supplementary_attestation_info_some (root : anyhow.Error → ErrRoot)
    (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8))
    (self : service.KeystoreService)
    (rl : RwLock (Option (alloc.vec.Vec Std.U8))) (hrl : globals.ENCODED_MODULE_INFO = ok rl)
    (g : RwLockReadGuard (Option (alloc.vec.Vec Std.U8))) (hread : RwLock.read rl = ok (.Ok g))
    (o : Option (alloc.vec.Vec Std.U8))
    (hderef : RwLockReadGuard.Insts.CoreOpsDerefDeref.deref g = ok o)
    (v : alloc.vec.Vec Std.U8)
    (hclone : core.option.Option.Insts.CoreCloneClone.clone
      (core.clone.CloneallocvecVec core.clone.CloneU8) o = ok (some v))
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (rc : ResponseCode.ResponseCode)
    (hrc : ResponseCode.ResponseCode.INFO_NOT_AVAILABLE = ok rc) :
    getSupp self (-1879047468)#i32 = ok (.Ok v)

recall get_supplementary_attestation_info_none (root : anyhow.Error → ErrRoot)
    (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8))
    (self : service.KeystoreService)
    (rl : RwLock (Option (alloc.vec.Vec Std.U8))) (hrl : globals.ENCODED_MODULE_INFO = ok rl)
    (g : RwLockReadGuard (Option (alloc.vec.Vec Std.U8))) (hread : RwLock.read rl = ok (.Ok g))
    (o : Option (alloc.vec.Vec Std.U8))
    (hderef : RwLockReadGuard.Insts.CoreOpsDerefDeref.deref g = ok o)
    (hclone : core.option.Option.Insts.CoreCloneClone.clone
      (core.clone.CloneallocvecVec core.clone.CloneU8) o = ok none)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (rc : ResponseCode.ResponseCode)
    (hrc : ResponseCode.ResponseCode.INFO_NOT_AVAILABLE = ok rc) :
    ∃ e, getSupp self (-1879047468)#i32 = ok (.Err e) ∧
      root e = ErrRoot.ks (error.Error.Rc rc)

end GetSupplementaryAttestationInfo

end Keystore2Verify.Service
