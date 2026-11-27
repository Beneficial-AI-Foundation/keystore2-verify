import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `utils`

New assumptions about external functions, and the shapes they share. Each assumption is a `Prop`:
nothing here is an axiom and nothing is proved. A theorem takes the assumptions it needs as
explicit hypotheses.

The adapter `FlatMap` is an opaque type in the translation. `Map` is a structure of the Aeneas
library with the fields `iter` and `f`, but `Iterator::map` and `Map::next` are declared only by
their types. Each assumption below constrains one external function and looks at an adapter only
through observations that the theorem takes as parameters: the iterator it reads from (`src`),
the state of its closure (`fn`) and, for `FlatMap`, the inner iterator it is working through
(`front`). For `Map`, the fields `iter` and `f` are such observations.
-/

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open core.iter.traits.iterator
open core.iter.traits.collect
open core.iter.adapters
open core.ops.function
open alloc.vec
open core.option.Option.Insts.CoreDefaultDefault renaming default → optionDefault
open core.option.Option.Insts.CoreCmpPartialEqOption renaming eq → optionEq
open core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator renaming next → mapNext
open core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator renaming
  next → flatMapNext

/-! ## Option -/

/-- Assumption about an external function: `default` returns `None` and does not panic. -/
def OptionDefaultAssumption {T : Type} (default : Result (Option T)) : Prop :=
  default = ok none

/-- Closed instance of `OptionDefaultAssumption` for `Option::<i32>::default()`. Record id
`ks2-ext-core-option-option-insts-coredefaultdefault-default`. -/
def OptionDefaultI32Spec : Prop :=
  OptionDefaultAssumption (optionDefault Std.I32)

/-- Assumption about an external function: `eq` on two options does not panic and returns `true`
exactly when the two options are equal. -/
def OptionEqAssumption {T : Type} [DecidableEq T]
    (eq : Option T → Option T → Result Bool) : Prop :=
  ∀ a b, eq a b = ok (decide (a = b))

/-- Closed instance of `OptionEqAssumption` for `Option::<i32>::eq` with the equality of `i32`.
Record id `ks2-ext-core-option-option-insts-corecmppartialeqoption-eq`. -/
def OptionEqI32Spec : Prop :=
  OptionEqAssumption
    (optionEq (T := Std.I32) core.cmp.PartialEqI32)

/-! ## Iterator adapters

The sources of both adapters are the iterator of a `Vec`. `IteratorVecIntoIter` and its `next`
are defined, so the assumptions use them directly. -/

/-- Assumption about an external function, over `Iterator::map` (`mapDefault`) on the iterator
of a `Vec`: the call does not panic, and the adapter it returns reads from the given iterator
and holds the given closure state. -/
def MapDefaultAssumption {A F : Type}
    (src : map.Map (into_iter.IntoIter A) F → into_iter.IntoIter A)
    (fn : map.Map (into_iter.IntoIter A) F → F)
    (mapDefault : into_iter.IntoIter A → F →
      Result (map.Map (into_iter.IntoIter A) F)) : Prop :=
  ∀ it f, ∃ m, mapDefault it f = ok m ∧ src m = it ∧ fn m = f

/-- Assumption about an external function, over `Map::next` (`next`) with the closure `call`:
one step of the adapter takes the next element `x` of the source and returns the closure result
on it, with the new source and the new closure state; at the end of the source it returns
`None`. Every statement is conditional on the calls inside the step returning normally. -/
def MapNextAssumption {A B F : Type}
    (src : map.Map (into_iter.IntoIter A) F → into_iter.IntoIter A)
    (fn : map.Map (into_iter.IntoIter A) F → F)
    (call : F → A → Result (B × F))
    (next : map.Map (into_iter.IntoIter A) F →
      Result (Option B × map.Map (into_iter.IntoIter A) F)) : Prop :=
  ∀ m i', (∀ x, into_iter.IteratorIntoIter.next (src m) = ok (some x, i') →
      ∀ y f', call (fn m) x = ok (y, f') →
        ∃ m', next m = ok (some y, m') ∧ src m' = i' ∧ fn m' = f') ∧
    (into_iter.IteratorIntoIter.next (src m) = ok (none, i') →
      ∃ m', next m = ok (none, m'))

/-- Closed instance of `MapDefaultAssumption` at the extracted `Iterator::map`. Record id
`ks2-ext-core-iter-traits-iterator-iterator-map-default`. -/
def MapDefaultSpec {A B F : Type} (fnInst : FnMut F A B)
    (src : map.Map (into_iter.IntoIter A) F → into_iter.IntoIter A)
    (fn : map.Map (into_iter.IntoIter A) F → F) : Prop :=
  MapDefaultAssumption src fn (Iterator.map.default (IteratorVecIntoIter A) fnInst)

/-- Closed instance of `MapNextAssumption` at the extracted `Map::next`. Record id
`ks2-ext-core-iter-adapters-map-map-insts-coreitertraitsiteratoriterator-next`. -/
def MapNextSpec {A B F : Type} (fnInst : FnMut F A B)
    (src : map.Map (into_iter.IntoIter A) F → into_iter.IntoIter A)
    (fn : map.Map (into_iter.IntoIter A) F → F) : Prop :=
  MapNextAssumption src fn fnInst.call_mut (mapNext (IteratorVecIntoIter A) fnInst)

/-- Assumption about an external function, over `Iterator::flat_map` (`flatMapDefault`) on the
iterator of a `Vec`: the call does not panic, and the adapter it returns reads from the given
iterator, holds the given closure state, has no inner iterator yet (`front m = none`), and is
`valid`. The predicate `valid` is a parameter: it holds of the states of forward iteration,
where no iterator is pending at the back of the adapter (the library adapter also has a back
iterator, which only `next_back` fills). -/
def FlatMapDefaultAssumption {A U F B : Type}
    (src : flatten.FlatMap (into_iter.IntoIter A) U F B U → into_iter.IntoIter A)
    (fn : flatten.FlatMap (into_iter.IntoIter A) U F B U → F)
    (front : flatten.FlatMap (into_iter.IntoIter A) U F B U → Option U)
    (valid : flatten.FlatMap (into_iter.IntoIter A) U F B U → Prop)
    (flatMapDefault : into_iter.IntoIter A → F →
      Result (flatten.FlatMap (into_iter.IntoIter A) U F B U)) : Prop :=
  ∀ it f, ∃ m, flatMapDefault it f = ok m ∧ src m = it ∧ fn m = f ∧ front m = none ∧ valid m

/-- Assumption about an external function, over `FlatMap::next` (`next`) with the outer closure
`call` and the `next` of the inner iterator (`innerNext`). While the adapter has an inner
iterator `j` (`front m = some j`), a step returns the next item of `j`; when `j` is exhausted the
adapter goes on as if it had no inner iterator. While it has none, it takes the next element of
the source and calls the closure, which gives the new inner iterator; at the end of the source
it returns `None`. Every statement is conditional on the calls inside the step returning
normally, and only for `valid` states: a step from a `valid` state that does not end the
iteration leads to `valid` states. Nothing is said about the state after the final `None`. -/
def FlatMapNextAssumption {A U F B : Type}
    (src : flatten.FlatMap (into_iter.IntoIter A) U F B U → into_iter.IntoIter A)
    (fn : flatten.FlatMap (into_iter.IntoIter A) U F B U → F)
    (front : flatten.FlatMap (into_iter.IntoIter A) U F B U → Option U)
    (valid : flatten.FlatMap (into_iter.IntoIter A) U F B U → Prop)
    (call : F → A → Result (U × F)) (innerNext : U → Result (Option B × U))
    (next : flatten.FlatMap (into_iter.IntoIter A) U F B U →
      Result (Option B × flatten.FlatMap (into_iter.IntoIter A) U F B U)) : Prop :=
  ∀ m, valid m →
    (∀ j, front m = some j → ∀ y j', innerNext j = ok (some y, j') →
      ∃ m', next m = ok (some y, m') ∧ src m' = src m ∧ fn m' = fn m ∧ front m' = some j' ∧
        valid m') ∧
    (∀ j, front m = some j → ∀ j', innerNext j = ok (none, j') →
      ∃ m', src m' = src m ∧ fn m' = fn m ∧ front m' = none ∧ valid m' ∧ next m = next m') ∧
    (front m = none → ∀ i', into_iter.IteratorIntoIter.next (src m) = ok (none, i') →
      ∃ m', next m = ok (none, m')) ∧
    (front m = none → ∀ x i', into_iter.IteratorIntoIter.next (src m) = ok (some x, i') →
      ∀ u f', call (fn m) x = ok (u, f') →
        ∃ m', src m' = i' ∧ fn m' = f' ∧ front m' = some u ∧ valid m' ∧ next m = next m')

/-- Closed instance of `FlatMapDefaultAssumption` at the extracted `Iterator::flat_map`. Record id
`ks2-ext-core-iter-traits-iterator-iterator-flat-map-default`. -/
def FlatMapDefaultSpec {A U F B : Type} (outer : FnMut F A U) (inner : Iterator U B)
    (src : flatten.FlatMap (into_iter.IntoIter A) U F B U → into_iter.IntoIter A)
    (fn : flatten.FlatMap (into_iter.IntoIter A) U F B U → F)
    (front : flatten.FlatMap (into_iter.IntoIter A) U F B U → Option U)
    (valid : flatten.FlatMap (into_iter.IntoIter A) U F B U → Prop) : Prop :=
  FlatMapDefaultAssumption src fn front valid
    (Iterator.flat_map.default (IteratorVecIntoIter A) (IntoIterator.Blanket inner) outer)

/-- Closed instance of `FlatMapNextAssumption` at the extracted `FlatMap::next`. Record id
`ks2-ext-core-iter-adapters-flatten-flatmap-insts-coreitertraitsiteratoriterator-next`. -/
def FlatMapNextSpec {A U F B : Type} (outer : FnMut F A U) (inner : Iterator U B)
    (src : flatten.FlatMap (into_iter.IntoIter A) U F B U → into_iter.IntoIter A)
    (fn : flatten.FlatMap (into_iter.IntoIter A) U F B U → F)
    (front : flatten.FlatMap (into_iter.IntoIter A) U F B U → Option U)
    (valid : flatten.FlatMap (into_iter.IntoIter A) U F B U → Prop) : Prop :=
  FlatMapNextAssumption src fn front valid outer.call_mut inner.next
    (flatMapNext (IteratorVecIntoIter A) (IntoIterator.Blanket inner) outer)

end Keystore2Verify.Utils
