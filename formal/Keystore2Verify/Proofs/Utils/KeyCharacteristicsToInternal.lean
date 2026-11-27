import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open utils.key_characteristics_to_internal
open Aeneas.Std.core.iter.traits.iterator renaming IteratorVecIntoIter → vecIntoIter
open keystore2.core.iter.adapters.map.Map.Insts renaming
  CoreIterTraitsIteratorIterator → mapIterator
open core.iter.adapters
open alloc.vec
open core.convert renaming IntoFrom.into → intoFrom
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open closure.closure.Insts renaming CoreOpsFunctionFnMutTupleKeyParameterKeyParameter → innerFnMut
open closure.Insts renaming
  CoreOpsFunctionFnMutTupleKeyCharacteristicsMapIntoIterKeyParameterGlobalclosure → outerFnMut
open key_parameter.KeyParameterValue.Insts renaming CoreConvertFromKeyParameter → valueFromKp

/-- conditional: `key_characteristics_to_internal` returns the parameters of all the entries of
`key_characteristics`, entry by entry in order and, within an entry, in the order of its
`authorizations`. The parameter made from an authorization `kp` of an entry `kc` has the value
that `into` makes from `kp` and the security level of `kc`; an empty input gives an empty result.
Hypotheses: the assumptions about external functions `MapDefaultSpec`, `MapNextSpec` (inner
`map`, with the observations `srcI` and `fnI`), `FlatMapDefaultSpec` and `FlatMapNextSpec`
(`flat_map`, with the observations `src`, `fn` and `front`, and the predicate `valid` of
forward-iteration states); for every authorization, that its
conversion returns normally (`hconv`: the extraction leaves `From<KeyParameter>` for
`KeyParameterValue` opaque); and that the total number of authorizations of all the entries
fits in a `usize` (`hbound`), as the collection into a vector requires. -/
theorem key_characteristics_to_internal_flat
    (srcI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      into_iter.IntoIter KeyParameter.KeyParameter)
    (fnI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      closure.closure)
    (src : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
    (fn : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → closure)
    (front : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      Option (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure))
    (valid : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → Prop)
    (hmapDef : MapDefaultSpec innerFnMut srcI fnI) (hmapNext : MapNextSpec innerFnMut srcI fnI)
    (hflatDef : FlatMapDefaultSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (hflatNext : FlatMapNextSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (key_characteristics : Vec KeyCharacteristics.KeyCharacteristics)
    (hconv : ∀ kc ∈ key_characteristics.val, ∀ kp ∈ kc.authorizations.val,
      ∃ v, intoFrom valueFromKp kp = ok v)
    (hbound : (key_characteristics.val.flatMap (fun kc => kc.authorizations.val)).length ≤
      Std.Usize.max) :
    ∃ out, utils.key_characteristics_to_internal key_characteristics = ok out ∧
      List.Forall₂ (fun (ckp : KeyCharacteristics.KeyCharacteristics × KeyParameter.KeyParameter)
          (r : key_parameter.KeyParameter) =>
        intoFrom valueFromKp ckp.2 = ok r.value ∧ r.security_level = ckp.1.securityLevel)
        (key_characteristics.val.flatMap
          (fun kc => (kc.authorizations).val.map (fun kp => (kc, kp)))) out.val := by
  sorry

/-- conditional: if the total number of authorizations of all the entries of `key_characteristics`
is larger than the largest `usize`, `key_characteristics_to_internal` fails with a panic: the
collection into a vector checks the size. Hypotheses: the same as for
`key_characteristics_to_internal_flat`, except that the bound is replaced by its opposite
(`hbig`). -/
theorem key_characteristics_to_internal_overflow
    (srcI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      into_iter.IntoIter KeyParameter.KeyParameter)
    (fnI : map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure →
      closure.closure)
    (src : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
    (fn : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → closure)
    (front : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) →
      Option (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure))
    (valid : flatten.FlatMap (into_iter.IntoIter KeyCharacteristics.KeyCharacteristics)
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) closure
      key_parameter.KeyParameter
      (map.Map (into_iter.IntoIter KeyParameter.KeyParameter) closure.closure) → Prop)
    (hmapDef : MapDefaultSpec innerFnMut srcI fnI) (hmapNext : MapNextSpec innerFnMut srcI fnI)
    (hflatDef : FlatMapDefaultSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (hflatNext : FlatMapNextSpec outerFnMut (mapIterator (vecIntoIter _) innerFnMut)
      src fn front valid)
    (key_characteristics : Vec KeyCharacteristics.KeyCharacteristics)
    (hconv : ∀ kc ∈ key_characteristics.val, ∀ kp ∈ kc.authorizations.val,
      ∃ v, intoFrom valueFromKp kp = ok v)
    (hbig : Std.Usize.max <
      (key_characteristics.val.flatMap (fun kc => kc.authorizations.val)).length) :
    utils.key_characteristics_to_internal key_characteristics = fail Error.panic := by
  sorry

end Keystore2Verify.Utils
