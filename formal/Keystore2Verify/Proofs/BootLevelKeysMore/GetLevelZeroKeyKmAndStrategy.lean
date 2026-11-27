import Keystore2Verify.Specs.Defs.BootLevelKeysMore

namespace Keystore2Verify.BootLevelKeysMore
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open Aeneas.Std.core.result.Result renaming Ok → ROk, Err → RErr
open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open SecurityLevel.SecurityLevel renaming TRUSTED_ENVIRONMENT → teeLevel,
  STRONGBOX → strongboxLevel
open boot_level_keys renaming get_level_zero_key_km_and_strategy → levelZero,
  lookup_level_zero_km_and_strategy → lookupLevel
open raw_device.KeyMintDevice renaming get → kmGet, get_or_none → kmGetOrNone,
  version → kmVersion

/-- conditional: if `lookup_level_zero_km_and_strategy` returns the error `e`,
`get_level_zero_key_km_and_strategy` returns an error with the same root class as `e`, with no
context added. In the Rust source this path returns before any other call. Hypothesis: that call
returns `ok (Err e)`. -/
theorem get_level_zero_key_km_and_strategy_lookup_error
    (root : anyhow.Error → ErrRoot) (e : anyhow.Error) (hl : lookupLevel = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e := by
  sorry

/-- conditional: if `lookup_level_zero_km_and_strategy` fails with `x`,
`get_level_zero_key_km_and_strategy` fails with `x`. Hypothesis: that call returns `fail x`. -/
theorem get_level_zero_key_km_and_strategy_lookup_fails
    (x : Error) (hl : lookupLevel = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the property gives the level `level` and the strategy `strategy`, and
`KeyMintDevice::get level` returns the device `dev`, the result is `(dev, strategy)`. In the
Rust source this path returns before version probing. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `lookup_level_zero_km_and_strategy` returns `ok (Ok (some (level,
strategy)))`; `get level` returns `ok (Ok dev)`. -/
theorem get_level_zero_key_km_and_strategy_from_property
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (level : SecurityLevel.SecurityLevel) (strategy : boot_level_keys.DenyLaterStrategy)
    (dev : KM) (hl : lookupLevel = ok (ROk (some (level, strategy))))
    (hg : kmGet level = ok (ROk dev)) :
    levelZero = ok (ROk (dev, strategy)) := by
  sorry

/-- conditional: if the property gives the level `level` and `KeyMintDevice::get level` returns the
error `e`, the result is an error with the context "Get KM instance failed." and the same root
cause as `e`. Hypotheses: `AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (the
code builds the message before `context` runs); `AnyCtxLaw root KM`; the two calls return as
stated. -/
theorem get_level_zero_key_km_and_strategy_from_property_get_error
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (level : SecurityLevel.SecurityLevel) (strategy : boot_level_keys.DenyLaterStrategy)
    (e : anyhow.Error) (hl : lookupLevel = ok (ROk (some (level, strategy))))
    (hg : kmGet level = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e := by
  sorry

/-- conditional: if the property gives the level `level` and `KeyMintDevice::get level` fails with
`x`, the result fails with `x`. Hypotheses: the two calls return as stated. -/
theorem get_level_zero_key_km_and_strategy_from_property_get_fails
    (level : SecurityLevel.SecurityLevel) (strategy : boot_level_keys.DenyLaterStrategy)
    (x : Error) (hl : lookupLevel = ok (ROk (some (level, strategy)))) (hg : kmGet level = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the property gives nothing and evaluating `SecurityLevel::TRUSTED_ENVIRONMENT`
fails with `x`, the result fails with `x`. Hypotheses: the two calls return as stated. -/
theorem get_level_zero_key_km_and_strategy_tee_level_fails
    (x : Error) (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the property gives nothing and `KeyMintDevice::get` of the TEE level returns the
error `e`, the result is an error with the context "Get TEE instance failed." and the same root
cause as `e`. Hypotheses: `AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (the
code builds the message before `context` runs); `AnyCtxLaw root KM`; the calls return as stated. -/
theorem get_level_zero_key_km_and_strategy_tee_get_error
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (e : anyhow.Error) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e := by
  sorry

/-- conditional: if the property gives nothing and `KeyMintDevice::get` of the TEE level fails with
`x`, the result fails with `x`. Hypotheses: the calls return as stated. -/
theorem get_level_zero_key_km_and_strategy_tee_get_fails
    (sl : SecurityLevel.SecurityLevel) (x : Error) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the property gives nothing, the TEE device is `tee` and `version tee` fails with
`x`, the result fails with `x`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `lookup_level_zero_km_and_strategy` returns `ok (Ok none)`;
`SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok (Ok tee)`; and
`version tee` returns `fail x`. -/
theorem get_level_zero_key_km_and_strategy_tee_version_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (x : Error)
    (hv : kmVersion tee = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the property gives nothing and the TEE device `tee` has a version of at least 41
(KeyMaster 4.1), the result is `(tee, EarlyBootOnly)`. In the Rust source the Strongbox device
is not asked on this path. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `lookup_level_zero_km_and_strategy` returns `ok (Ok none)`;
`SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok (Ok tee)`;
`version tee` returns `ok i` with `41 ≤ i`. -/
theorem get_level_zero_key_km_and_strategy_tee_new_enough
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (i : Std.I32)
    (hv : kmVersion tee = ok i) (hi : 41 ≤ i.val) :
    levelZero = ok (ROk (tee, boot_level_keys.DenyLaterStrategy.EarlyBootOnly)) := by
  sorry

/-- conditional: if the TEE device is older than 41 and evaluating `SecurityLevel::STRONGBOX` fails
with `x`, the result fails with `x`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `lookup_level_zero_km_and_strategy` returns `ok (Ok none)`;
`SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok (Ok tee)`;
`version tee` returns `ok i` with `i < 41`; and `SecurityLevel::STRONGBOX` returns `fail x`. -/
theorem get_level_zero_key_km_and_strategy_strongbox_level_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (i : Std.I32)
    (hv : kmVersion tee = ok i) (hi : i.val < 41) (x : Error) (hS : strongboxLevel = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the TEE device is older than 41 and `KeyMintDevice::get_or_none` of the
Strongbox level returns the error `e`, the result is an error with the context "Get Strongbox
instance failed." and the same root cause as `e`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `AnyCtxLaw root (Option KM)`; `lookup_level_zero_km_and_strategy` returns
`ok (Ok none)`; `SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok
(Ok tee)`; `version tee` returns `ok i` with `i < 41`; `STRONGBOX` evaluates to `ok sl2`;
`get_or_none sl2` returns `ok (Err e)`. -/
theorem get_level_zero_key_km_and_strategy_strongbox_error
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (e : anyhow.Error)
    (hs : kmGetOrNone sl2 = ok (RErr e)) :
    ∃ e', levelZero = ok (RErr e') ∧ root e' = root e := by
  sorry

/-- conditional: if the TEE device is older than 41 and `get_or_none` of the Strongbox level fails
with `x`, the result fails with `x`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `lookup_level_zero_km_and_strategy` returns `ok (Ok none)`;
`SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok (Ok tee)`;
`version tee` returns `ok i` with `i < 41`; `STRONGBOX` evaluates to `ok sl2`; `get_or_none sl2`
returns `fail x`. -/
theorem get_level_zero_key_km_and_strategy_strongbox_get_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (sl : SecurityLevel.SecurityLevel) (tee : KM) (hl : lookupLevel = ok (ROk none))
    (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee)) (i : Std.I32)
    (hv : kmVersion tee = ok i) (hi : i.val < 41) (sl2 : SecurityLevel.SecurityLevel)
    (hS : strongboxLevel = ok sl2) (x : Error) (hs : kmGetOrNone sl2 = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the TEE device is older than 41 and there is no Strongbox device, the result is
`(tee, MaxUsesPerBoot)`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `AnyCtxLaw root (Option KM)`; `lookup_level_zero_km_and_strategy` returns
`ok (Ok none)`; `SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok
(Ok tee)`; `version tee` returns `ok i` with `i < 41`; `STRONGBOX` evaluates to `ok sl2`;
`get_or_none sl2` returns `ok (Ok none)`. -/
theorem get_level_zero_key_km_and_strategy_no_strongbox
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2)
    (hs : kmGetOrNone sl2 = ok (ROk none)) :
    levelZero = ok (ROk (tee, boot_level_keys.DenyLaterStrategy.MaxUsesPerBoot)) := by
  sorry

/-- conditional: if the TEE device is older than 41, the Strongbox device is `sb` and `version sb`
fails with `x`, the result fails with `x`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `AnyCtxLaw root (Option KM)`; `lookup_level_zero_km_and_strategy` returns
`ok (Ok none)`; `SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok
(Ok tee)`; `version tee` returns `ok i` with `i < 41`; `STRONGBOX` evaluates to `ok sl2`;
`get_or_none sl2` returns `ok (Ok (some sb))`; `version sb` returns `fail x`. -/
theorem get_level_zero_key_km_and_strategy_strongbox_version_fails
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (sb : KM)
    (hs : kmGetOrNone sl2 = ok (ROk (some sb))) (x : Error) (hv2 : kmVersion sb = fail x) :
    levelZero = fail x := by
  sorry

/-- conditional: if the TEE device is older than 41 and the Strongbox device `sb` has a version of
at least 41, the result is `(sb, EarlyBootOnly)`: the TEE device is dropped. Hypotheses:
`AllocFmtFormatSpec` and `CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message
before `context` runs); `AnyCtxLaw root KM`; `AnyCtxLaw root (Option KM)`;
`lookup_level_zero_km_and_strategy` returns `ok (Ok none)`; `SecurityLevel::TRUSTED_ENVIRONMENT`
evaluates to `ok sl`; `get sl` returns `ok (Ok tee)`; `version tee` returns `ok i` with `i <
41`; `STRONGBOX` evaluates to `ok sl2`; `get_or_none sl2` returns `ok (Ok (some sb))`; `version
sb` returns `ok j` with `41 ≤ j`. -/
theorem get_level_zero_key_km_and_strategy_strongbox_new_enough
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (sb : KM)
    (hs : kmGetOrNone sl2 = ok (ROk (some sb))) (j : Std.I32) (hv2 : kmVersion sb = ok j)
    (hj : 41 ≤ j.val) :
    levelZero = ok (ROk (sb, boot_level_keys.DenyLaterStrategy.EarlyBootOnly)) := by
  sorry

/-- conditional: if the TEE device is older than 41 and the Strongbox device `sb` is older than 41
too, the result is `(tee, MaxUsesPerBoot)`. Hypotheses: `AllocFmtFormatSpec` and
`CoreFmtArgumentsFromStrNonconstSpec` (the code builds the message before `context` runs);
`AnyCtxLaw root KM`; `AnyCtxLaw root (Option KM)`; `lookup_level_zero_km_and_strategy` returns
`ok (Ok none)`; `SecurityLevel::TRUSTED_ENVIRONMENT` evaluates to `ok sl`; `get sl` returns `ok
(Ok tee)`; `version tee` returns `ok i` with `i < 41`; `STRONGBOX` evaluates to `ok sl2`;
`get_or_none sl2` returns `ok (Ok (some sb))`; `version sb` returns `ok j` with `j < 41`. -/
theorem get_level_zero_key_km_and_strategy_strongbox_too_old
    (root : anyhow.Error → ErrRoot) (hFmt : AllocFmtFormatSpec)
    (hArg : CoreFmtArgumentsFromStrNonconstSpec) (hCtx : AnyCtxLaw root KM)
    (hCtx2 : AnyCtxLaw root (Option KM)) (sl : SecurityLevel.SecurityLevel) (tee : KM)
    (hl : lookupLevel = ok (ROk none)) (hT : teeLevel = ok sl) (hg : kmGet sl = ok (ROk tee))
    (i : Std.I32) (hv : kmVersion tee = ok i) (hi : i.val < 41)
    (sl2 : SecurityLevel.SecurityLevel) (hS : strongboxLevel = ok sl2) (sb : KM)
    (hs : kmGetOrNone sl2 = ok (ROk (some sb))) (j : Std.I32) (hv2 : kmVersion sb = ok j)
    (hj : j.val < 41) :
    levelZero = ok (ROk (tee, boot_level_keys.DenyLaterStrategy.MaxUsesPerBoot)) := by
  sorry

end Keystore2Verify.BootLevelKeysMore
