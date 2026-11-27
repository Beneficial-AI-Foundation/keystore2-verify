import Keystore2Verify.Proofs.BootLevelKeysMore.DenyLaterStrategy
import Keystore2Verify.Proofs.BootLevelKeysMore.GetLevelZeroKeyKmAndStrategy

namespace Keystore2Verify.BootLevelKeysMore

section DenyLaterStrategy
open Aeneas Aeneas.Std Result keystore2
open boot_level_keys.DenyLaterStrategy.Insts
open CoreCmpPartialEqDenyLaterStrategy renaming eq → strategyEq
open CoreCloneClone renaming clone → strategyClone

recall deny_later_strategy_eq (a b : boot_level_keys.DenyLaterStrategy) :
    ∃ r, strategyEq a b = ok r ∧ (r = true ↔ a = b)

recall deny_later_strategy_clone (s : boot_level_keys.DenyLaterStrategy) :
    strategyClone s = ok s

end DenyLaterStrategy

section GetLevelZeroKeyKmAndStrategy
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open SecurityLevel.SecurityLevel renaming TRUSTED_ENVIRONMENT → teeLevel,
  STRONGBOX → strongboxLevel
open boot_level_keys renaming get_level_zero_key_km_and_strategy → levelZero,
  lookup_level_zero_km_and_strategy → lookupLevel
open raw_device.KeyMintDevice renaming get → kmGet, get_or_none → kmGetOrNone,
  version → kmVersion

recall get_level_zero_key_km_and_strategy_lookup_error
    (root : anyhow.Error → ErrRoot) (e : anyhow.Error) (hl : lookupLevel = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e

recall get_level_zero_key_km_and_strategy_lookup_fails
    (x : Error) (hl : lookupLevel = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_from_property
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (level : SecurityLevel.SecurityLevel) (strategy : boot_level_keys.DenyLaterStrategy)
    (dev : KM) (hl : lookupLevel = ok (ROk (some (level, strategy))))
    (hg : kmGet level = ok (ROk dev)) :
    levelZero = ok (ROk (dev, strategy))

recall get_level_zero_key_km_and_strategy_from_property_get_error
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (level : SecurityLevel.SecurityLevel) (strategy : boot_level_keys.DenyLaterStrategy)
    (e : anyhow.Error) (hl : lookupLevel = ok (ROk (some (level, strategy))))
    (hg : kmGet level = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e

recall get_level_zero_key_km_and_strategy_from_property_get_fails
    (level : SecurityLevel.SecurityLevel) (strategy : boot_level_keys.DenyLaterStrategy)
    (x : Error) (hl : lookupLevel = ok (ROk (some (level, strategy)))) (hg : kmGet level = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_tee_level_fails
    (x : Error) (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_tee_get_error
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (e : anyhow.Error) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e

recall get_level_zero_key_km_and_strategy_tee_get_fails
    (sl : SecurityLevel.SecurityLevel) (x : Error) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_tee_version_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (x : Error)
    (hv : kmVersion tee = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_tee_new_enough
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (i : Std.I32)
    (hv : kmVersion tee = ok i) (hi : 41 ≤ i.val) :
    levelZero = ok (ROk (tee, boot_level_keys.DenyLaterStrategy.EarlyBootOnly))

recall get_level_zero_key_km_and_strategy_strongbox_level_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (i : Std.I32)
    (hv : kmVersion tee = ok i) (hi : i.val < 41) (x : Error) (hS : strongboxLevel = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_strongbox_error
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (e : anyhow.Error)
    (hs : kmGetOrNone sl2 = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e

recall get_level_zero_key_km_and_strategy_strongbox_get_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (i : Std.I32)
    (hv : kmVersion tee = ok i) (hi : i.val < 41) (sl2 : SecurityLevel.SecurityLevel)
    (hS : strongboxLevel = ok sl2) (x : Error) (hs : kmGetOrNone sl2 = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_no_strongbox
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2)
    (hs : kmGetOrNone sl2 = ok (ROk none)) :
    levelZero = ok (ROk (tee, boot_level_keys.DenyLaterStrategy.MaxUsesPerBoot))

recall get_level_zero_key_km_and_strategy_strongbox_version_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (sb : KM)
    (hs : kmGetOrNone sl2 = ok (ROk (some sb))) (x : Error) (hv2 : kmVersion sb = fail x) :
    levelZero = fail x

recall get_level_zero_key_km_and_strategy_strongbox_new_enough
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (sb : KM)
    (hs : kmGetOrNone sl2 = ok (ROk (some sb))) (j : Std.I32) (hv2 : kmVersion sb = ok j)
    (hj : 41 ≤ j.val) :
    levelZero = ok (ROk (sb, boot_level_keys.DenyLaterStrategy.EarlyBootOnly))

recall get_level_zero_key_km_and_strategy_strongbox_too_old
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (sb : KM)
    (hs : kmGetOrNone sl2 = ok (ROk (some sb))) (j : Std.I32) (hv2 : kmVersion sb = ok j)
    (hj : j.val < 41) :
    levelZero = ok (ROk (tee, boot_level_keys.DenyLaterStrategy.MaxUsesPerBoot))

end GetLevelZeroKeyKmAndStrategy

end Keystore2Verify.BootLevelKeysMore
