import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open core.result.ResultTError.Insts.Keystore2DatabaseDoGc renaming do_gc → doGc
open core.result.ResultTError.Insts.Keystore2DatabaseDoGc renaming no_gc → noGc
open core.result.ResultTError.Insts.Keystore2DatabaseDoGc renaming need_gc → needGc

/-- exact: `do_gc` never fails. It pairs the flag with the value of an `Ok`. An `Err` stays an
`Err` with the same root cause (`root`, the classifier of `anyhow::Error`). -/
theorem do_gc_result {T : Type} (root : anyhow.Error → ErrRoot) :
    (∀ (v : T) (b : Bool),
      doGc (.Ok v : core.result.Result T anyhow.Error) b = ok (.Ok (b, v))) ∧
    (∀ (e : anyhow.Error) (b : Bool), ∃ e',
      doGc (.Err e : core.result.Result T anyhow.Error) b = ok (.Err e') ∧ root e' = root e) := by
  sorry

/-- exact: `no_gc` never fails. It pairs `false` with the value of an `Ok`. An `Err` stays an
`Err` with the same root cause (`root`). -/
theorem no_gc_result {T : Type} (root : anyhow.Error → ErrRoot) :
    (∀ v : T, noGc (.Ok v : core.result.Result T anyhow.Error) = ok (.Ok (false, v))) ∧
    (∀ e : anyhow.Error, ∃ e',
      noGc (.Err e : core.result.Result T anyhow.Error) = ok (.Err e') ∧ root e' = root e) := by
  sorry

/-- exact: `need_gc` never fails. It pairs `true` with the value of an `Ok`. An `Err` stays an
`Err` with the same root cause (`root`). -/
theorem need_gc_result {T : Type} (root : anyhow.Error → ErrRoot) :
    (∀ v : T, needGc (.Ok v : core.result.Result T anyhow.Error) = ok (.Ok (true, v))) ∧
    (∀ e : anyhow.Error, ∃ e',
      needGc (.Err e : core.result.Result T anyhow.Error) = ok (.Err e') ∧ root e' = root e) := by
  sorry
