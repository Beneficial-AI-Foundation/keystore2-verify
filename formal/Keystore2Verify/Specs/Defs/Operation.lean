import Keystore2Verify.Specs.Defs.Externals
import Keystore2Verify.Specs.Defs.ExternalsMore

/-!
# Definitions for the statements about `operation.rs`

The assumptions about three external functions that the paths of `check_input_length` and
`OperationDb::get` evaluate. Nothing here is an axiom.
-/

namespace Keystore2Verify.Operation
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open operation.OperationDb.get.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleShared0WeakOperationGlobalOptionArcOperation → getClosure

/-- Assumption about an external function, over the function `new`: for every marker `t` and
keystore2 error `x`, `new t x` never panics, and the error it returns has the root cause `x`, of
class `ErrRoot.ks x`. This is the macro `anyhow!(x)` for an error type that implements
`std::error::Error` and has no `source`: it calls `Error::from_std`. Idealisation: allocation
never fails.
Record `ks2-ext-anyhow-kind-trait-new`. -/
def AnyhowKindTraitNewAssumption (root : anyhow.Error → ErrRoot)
    (new : anyhow.kind.Trait → error.Error → Result anyhow.Error) : Prop :=
  ∀ (t : anyhow.kind.Trait) (x : error.Error),
    ∃ e, new t x = ok e ∧ root e = ErrRoot.ks x

/-- The closed instance of `AnyhowKindTraitNewAssumption` for `anyhow::kind::Trait::new` at the
conversion that `anyhow!` uses (record `ks2-ext-anyhow-kind-trait-new`). -/
def AnyhowKindTraitNewSpec (root : anyhow.Error → ErrRoot) : Prop :=
  AnyhowKindTraitNewAssumption root (anyhow.kind.Trait.new
    (core.convert.IntoFrom (anyhow.Error.Insts.CoreConvertFrom error.Error.Insts.CoreErrorError)))

/-- Assumption about an external function, over the function `must_use`: the call never panics and
returns its argument. -/
def AnyhowMustUseAssumption (must_use : anyhow.Error → Result anyhow.Error) : Prop :=
  ∀ e : anyhow.Error, must_use e = ok e

/-- `anyhow::__private::must_use` never panics and returns its argument: the shared assumption about
this external function, `ExternalsMore.AnyhowMustUseSpec`. -/
abbrev AnyhowMustUseSpec : Prop := ExternalsMore.AnyhowMustUseSpec

/-- Assumption about an external function, over the function `and_then` and the closure instance
`inst`: on `None` the call returns `None`; on `Some x` it returns the result of calling the
closure on `x`.
Record `ks2-ext-core-option-option-and-then`. -/
def OptionAndThenAssumption {T U F : Type} (inst : core.ops.function.FnOnce F T (Option U))
    (and_then : Option T → F → Result (Option U)) : Prop :=
  ∀ f, and_then none f = ok none ∧ ∀ x, and_then (some x) f = inst.call_once f x

/-- The closed instance of `OptionAndThenAssumption` for `Option::and_then` at the closure of
`OperationDb::get` (record `ks2-ext-core-option-option-and-then`). -/
def OptionAndThenSpec : Prop :=
  OptionAndThenAssumption getClosure (core.option.Option.and_then getClosure)

end Keystore2Verify.Operation
