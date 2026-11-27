import Keystore2Verify.Specs.Defs.AttestationKeyUtils

namespace Keystore2Verify.Service
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals Keystore2Verify.AttestationKeyUtils
open Keystore2Verify.Permission (invalidArgumentError)
open android_system_keystore2.aidl.android.system.keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open service.KeystoreService renaming get_supplementary_attestation_info → getSupp
open std.sync.poison.rwlock

/-- conditional: for a tag other than `MODULE_HASH` (-1879047468), the result is an error whose root
cause is the keystore2 error `Rc(INVALID_ARGUMENT)`. Hypotheses: `format` does not fail; the
assumption about `context` for a keystore2 error (`KsCtxAssumption`). -/
theorem get_supplementary_attestation_info_other (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hks : KsCtxAssumption root (alloc.vec.Vec Std.U8))
    (self : service.KeystoreService) (tag : Tag.Tag) (h : tag ≠ (-1879047468)#i32) :
    ∃ e, getSupp self tag = ok (.Err e) ∧ root e = ErrRoot.ks invalidArgumentError := by
  sorry

/-- conditional: for `MODULE_HASH`, if the lock of the stored module information cannot be read
(the lock is poisoned), `get_supplementary_attestation_info` panics (`unwrap`): it returns `fail`.
Hypotheses: the outcomes of `ENCODED_MODULE_INFO` and of `RwLock::read`. -/
theorem get_supplementary_attestation_info_poisoned (self : service.KeystoreService)
    (rl : RwLock (Option (alloc.vec.Vec Std.U8))) (hrl : globals.ENCODED_MODULE_INFO = ok rl)
    (pe : std.sync.poison.PoisonError (RwLockReadGuard (Option (alloc.vec.Vec Std.U8))))
    (hread : RwLock.read rl = ok (.Err pe)) :
    getSupp self (-1879047468)#i32 = fail Error.panic := by
  sorry

/-- conditional: for `MODULE_HASH`, if the stored module information is `Some v`,
`get_supplementary_attestation_info` returns `Ok v`. Hypotheses: the outcomes of
`ENCODED_MODULE_INFO`, of `RwLock::read` (the guard `g`), of the dereference of `g` (the option
`o`) and of the clone of `o` (which is `Some v`); `format` and `from_str_nonconst` do not fail;
the outcome of the constant `ResponseCode::INFO_NOT_AVAILABLE`; the assumption about `context`
for a keystore2 error (`KsCtxAssumption`). -/
theorem get_supplementary_attestation_info_some (root : anyhow.Error → ErrRoot)
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
    getSupp self (-1879047468)#i32 = ok (.Ok v) := by
  sorry

/-- conditional: for `MODULE_HASH`, if no module information was received (the clone of the stored
option is `None`), the result is an error whose root cause is the keystore2 error
`Rc(INFO_NOT_AVAILABLE)`. Hypotheses: the outcomes of `ENCODED_MODULE_INFO`, of `RwLock::read`
(the guard `g`), of the dereference of `g` and of the clone of the option (which is `None`); the
constant `ResponseCode::INFO_NOT_AVAILABLE` is `rc`; `format` and `from_str_nonconst` do not fail;
the assumption about `context` for a keystore2 error (`KsCtxAssumption`). -/
theorem get_supplementary_attestation_info_none (root : anyhow.Error → ErrRoot)
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
      root e = ErrRoot.ks (error.Error.Rc rc) := by
  sorry
