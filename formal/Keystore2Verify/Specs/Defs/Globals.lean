import Keystore2Verify.Specs.Defs.Externals

/-! # Definitions for the statements about `globals.rs` and `super_key.rs`

The hash maps, the `Option` helpers and the clones that these two files use are declared only by
their type in the translation. This file states what the statements assume about them. It contains
definitions only: nothing here is an axiom and nothing is proved.

* A hash map `HashMap K V` is opaque. An assumption takes the observation `ents`, the list of its
  `(key, value)` entries, as a parameter. Nothing is said about the order of the entries.
* An assumption says only as much as the statements need. Each assumption cites the record of the
  function it is about, and an effect (a lock, a service call, a random number) is never assumed
  here: the statements take such an outcome as an inline hypothesis.
* Idealisation: allocation never fails. An assumption that says a call does not fail holds for
  the real functions only while memory lasts.

The `Specs.Defs.SuperKey` file reuses the assumptions of this file. -/

namespace Keystore2Verify.Globals
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay
open anyhow.Error.Insts renaming CoreConvertFrom → anyhowFrom
open binder.StatusCode.Insts renaming CoreErrorError → statusErrorError
open binder.Strong.Insts
open core.iter.adapters.map
open core.iter.adapters.map.Map.Insts
open core.iter.traits.iterator
open core.iter.traits.iterator.Iterator
open core.ops.function
open core.option
open core.option.Option.Insts
open std.collections.hash.map
open std.collections.hash.map.Values.Insts
open std.hash.random

/-! ## Hash maps -/

/-- The hash map type that both files use: the default hasher and the global allocator. -/
abbrev HMap (K V : Type) : Type :=
  HashMap K V RandomState alloc.alloc.Global

/-- The observation of a hash map: the list of its entries. -/
abbrev Entries (K V : Type) : Type := HMap K V → List (K × V)

/-- The entries of `m'` are those of `m` with the key `k` bound to `v`: every entry of `m` with
another key stays, and the entry with the key `k` is `(k, v)`. -/
def MapUpdate {K V : Type} (ents : Entries K V) (m m' : HMap K V) (k : K) (v : V) : Prop :=
  ∀ e, e ∈ ents m' ↔ e = (k, v) ∨ (e ∈ ents m ∧ e.1 ≠ k)

/-- Assumption about `HashMap::get` (register record
`ks2-ext-std-collections-hash-map-hashmap-get`). `get m k` never panics, and it returns `some v`
exactly when `(k, v)` is an entry. The keys of the maps in these files are compared by an `Eq`
that is equality of values. Idealisation: hashing never panics. -/
def HashMapGetAssumption {K V : Type} (ents : Entries K V)
    (get : HMap K V → K → Result (Option V)) : Prop :=
  ∀ m k, ∃ r, get m k = ok r ∧ ∀ v, r = some v ↔ (k, v) ∈ ents m

/-- Assumption about `HashMap::insert` (register record
`ks2-ext-std-collections-hash-map-hashmap-insert`). `insert m k v` never panics, and the map it
returns binds `k` to `v` and keeps every other entry. The returned old value is not assumed.
Idealisation: allocation never fails, and a full map can grow. -/
def HashMapInsertAssumption {K V : Type} (ents : Entries K V)
    (insert : HMap K V → K → V → Result (Option V × HMap K V)) : Prop :=
  ∀ m k v, ∃ old m', insert m k v = ok (old, m') ∧ MapUpdate ents m m' k v

/-- The function `mk` makes a hash map from nothing: the call never panics and the map it returns
has no entry. The random state is not observed. This predicate cites no record; the two
assumptions below do. -/
def HashMapEmptyAssumption {K V : Type} (ents : Entries K V) (mk : Result (HMap K V)) : Prop :=
  ∃ m, mk = ok m ∧ ents m = []

/-- Assumption about `HashMap::new` (register record
`ks2-ext-std-collections-hash-map-hashmapkvrandomstateglobal-new`): the call never panics and the
map it returns has no entry. -/
def HashMapNewAssumption {K V : Type} (ents : Entries K V) (mk : Result (HMap K V)) : Prop :=
  HashMapEmptyAssumption ents mk

/-- Assumption about `Default::default` of a hash map (register record
`ks2-ext-std-collections-hash-map-hashmapkvsglobal-insts-coredefaultdefault-default`): the call
never panics and the map it returns has no entry. -/
def HashMapDefaultAssumption {K V : Type} (ents : Entries K V) (mk : Result (HMap K V)) :
    Prop :=
  HashMapEmptyAssumption ents mk

/-- The iterator over the values of a hash map. -/
abbrev Vals (K V : Type) : Type := Values K V

/-- Assumption about `HashMap::values` (register record
`ks2-ext-std-collections-hash-map-hashmap-values`). `values m` never panics. The values that the
returned iterator has left, `elems it` in the order of iteration, are the values of the entries of
`m`, each as many times as it occurs. -/
def HashMapValuesAssumption {K V : Type} (ents : Entries K V) (elems : Vals K V → List V)
    (values : HMap K V → Result (Vals K V)) : Prop :=
  ∀ m, ∃ it, values m = ok it ∧ (elems it).Perm ((ents m).map Prod.snd)

/-- Assumption about `next` of the `Values` iterator (register record
`ks2-ext-std-collections-hash-map-values-insts-coreitertraitsiteratoriteratorsharedav-next`).
`next it` never panics. It returns the first value that is left and an iterator that has the
rest, or `None` when no value is left. -/
def ValuesNextAssumption {K V : Type} (elems : Vals K V → List V)
    (next : Vals K V → Result (Option V × Vals K V)) : Prop :=
  ∀ it, (elems it = [] → ∃ it', next it = ok (none, it')) ∧
    ∀ x xs, elems it = x :: xs → ∃ it', next it = ok (some x, it') ∧ elems it' = xs

/-! ## Iterator adapters -/

/-- Assumption about `Iterator::map` (register record
`ks2-ext-core-iter-traits-iterator-iterator-map-default`). `map i f` never panics, and it pairs the
iterator with the function. -/
def IteratorMapAssumption {I F : Type} (map : I → F → Result (Map I F)) :
    Prop :=
  ∀ i f, map i f = ok ⟨i, f⟩

/-- Assumption about `next` of the `Map` adapter (register record
`ks2-ext-core-iter-adapters-map-map-insts-coreitertraitsiteratoriterator-next`). `next` of the
adapter takes the next item of the inner iterator and applies the function to it, as the
standard library does. -/
def IterMapNextAssumption {I F A B : Type} (it : Iterator I A)
    (fm : FnMut F A B)
    (next : Map I F →
      Result (Option B × Map I F)) : Prop :=
  ∀ i f, next ⟨i, f⟩ = (do
    let (o, i') ← it.next i
    match o with
    | none => ok (none, ⟨i', f⟩)
    | some x => do
      let (y, f') ← fm.call_mut f x
      ok (some y, ⟨i', f'⟩))

/-! ## `Option` helpers and clones -/

/-- Assumption about `Option::and_then` (register record `ks2-ext-core-option-option-and-then`).
`and_then none f` is `None`, and `and_then (some x) f` is the result of calling `f` on `x`. -/
def OptionAndThenAssumption {T U F : Type} (fo : FnOnce F T (Option U))
    (and_then : Option T → F → Result (Option U)) : Prop :=
  ∀ f, and_then none f = ok none ∧ ∀ x, and_then (some x) f = fo.call_once f x

/-- Assumption about `Option::as_ref` (register record `ks2-ext-core-option-option-as-ref`). The
call never panics and returns the same option. -/
def OptionAsRefSpec (T : Type) : Prop :=
  ∀ o : Option T, Option.as_ref o = ok o

/-- Assumption about `Option::default` (register record
`ks2-ext-core-option-option-insts-coredefaultdefault-default`). The call never panics and returns
`None`. -/
def OptionDefaultSpec (T : Type) : Prop :=
  CoreDefaultDefault.default T = ok none

/-- Assumption about the clone of a binder handle (register record
`ks2-ext-binder-strong-insts-corecloneclone-clone`). The call never panics and returns the same
handle. Idealisation: the count of references does not overflow. -/
def StrongCloneSpec {T : Type} (inst : binder.FromIBinder T) : Prop :=
  ∀ d, CoreCloneClone.clone inst d = ok d

open android_hardware_security_keymint.aidl.android.hardware.security.keymint in
/-- The hardware information of a KeyMint device. -/
abbrev KmHwInfo : Type := KeyMintHardwareInfo.KeyMintHardwareInfo

open android_hardware_security_keymint.aidl.android.hardware.security.keymint in
open KeyMintHardwareInfo.KeyMintHardwareInfo.Insts.CoreCloneClone renaming clone → hwInfoClone in
/-- Assumption about the clone of the hardware information (register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-keyminthardwareinfo-keyminthardwareinfo-insts-corecloneclone-clone`).
The call never panics and returns an equal value. Idealisation: allocation never fails. -/
def KmHwInfoCloneSpec : Prop :=
  ∀ h, hwInfoClone h = ok h

open android_hardware_security_keymint.aidl.android.hardware.security.keymint.SecurityLevel in
/-- The security level type of KeyMint. -/
abbrev SecLevel : Type := SecurityLevel

/-! ## The map of KeyMint devices

The closed instances of the assumptions above, at the two maps of `DevicesMap<T>`. -/

/-- A KeyMint device with its hardware information, as the map `devices_by_uuid` stores it. -/
abbrev Device (T : Type) : Type := binder.Strong T × KmHwInfo

open database.Uuid.Insts renaming CoreCmpEq → uuidEq, CoreHashHash → uuidHash
open RandomState.Insts renaming CoreHashBuildHasherDefaultHasher → rsHasher
open core.borrow.Borrow renaming Blanket → borrowSelf

/-- `HashMap::get` on `devices_by_uuid`. -/
abbrev DevicesGetSpec {T : Type} (ents : Entries database.Uuid (Device T)) : Prop :=
  HashMapGetAssumption ents
    (HashMap.get uuidEq uuidHash rsHasher (borrowSelf database.Uuid)
      uuidHash uuidEq)

open android_hardware_security_keymint.aidl.android.hardware.security.keymint.SecurityLevel in
open SecurityLevel.Insts renaming CoreCmpEq → secEq, CoreHashHash → secHash in
/-- `HashMap::get` on `uuid_by_sec_level`. -/
abbrev SecLevelGetSpec (ents : Entries SecLevel database.Uuid) : Prop :=
  HashMapGetAssumption ents
    (HashMap.get secEq secHash rsHasher (borrowSelf SecLevel)
      secHash secEq)

/-- `HashMap::insert` on `devices_by_uuid`. -/
abbrev DevicesInsertSpec {T : Type} (ents : Entries database.Uuid (Device T)) : Prop :=
  HashMapInsertAssumption ents (HashMap.insert uuidEq uuidHash rsHasher)

open android_hardware_security_keymint.aidl.android.hardware.security.keymint.SecurityLevel in
open SecurityLevel.Insts renaming CoreCmpEq → secEq, CoreHashHash → secHash in
/-- `HashMap::insert` on `uuid_by_sec_level`. -/
abbrev SecLevelInsertSpec (ents : Entries SecLevel database.Uuid) : Prop :=
  HashMapInsertAssumption ents (HashMap.insert secEq secHash rsHasher)

open globals.DevicesMap.dev_by_sec_level.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0UuidOptionTupleStrongKeyMintHardwareInfoUuid → bySecLevelFnOnce
in
/-- `Option::and_then` at the call of `dev_by_sec_level`. -/
abbrev DevBySecLevelAndThenSpec {T : Type} (inst : binder.FromIBinder T) : Prop :=
  OptionAndThenAssumption (bySecLevelFnOnce inst)
    (Option.and_then (bySecLevelFnOnce inst))

open globals.DevicesMap.devices.closure.Insts renaming
  CoreOpsFunctionFnMutTupleShared0PairStrongKeyMintHardwareInfoPairStrongSecurityLevel →
    devicesFnMut
open Values.Insts renaming
  CoreIterTraitsIteratorIteratorSharedAV → valuesIter

/-- `HashMap::values` on `devices_by_uuid`. -/
abbrev DevicesValuesSpec {T : Type} (ents : Entries database.Uuid (Device T))
    (elems : Vals database.Uuid (Device T) → List (Device T)) : Prop :=
  HashMapValuesAssumption ents elems HashMap.values

/-- `next` of the `Values` iterator over the devices. -/
abbrev DevicesValuesNextSpec {T : Type}
    (elems : Vals database.Uuid (Device T) → List (Device T)) : Prop :=
  ValuesNextAssumption elems
    (CoreIterTraitsIteratorIteratorSharedAV.next
      (K := database.Uuid) (V := Device T))

/-- `Iterator::map` over the values of `devices_by_uuid` with the closure of `devices`. -/
abbrev DevicesMapSpec {T : Type} (inst : binder.FromIBinder T) : Prop :=
  IteratorMapAssumption (map.default
    (valuesIter database.Uuid (Device T)) (devicesFnMut inst))

/-- `next` of the `Map` adapter over the values of `devices_by_uuid`. -/
abbrev DevicesMapNextSpec {T : Type} (inst : binder.FromIBinder T) : Prop :=
  IterMapNextAssumption (valuesIter database.Uuid (Device T)) (devicesFnMut inst)
    (CoreIterTraitsIteratorIterator.next
      (valuesIter database.Uuid (Device T)) (devicesFnMut inst))

/-! ## Errors and context calls -/

open android_hardware_security_keymint.aidl.android.hardware.security.keymint.ErrorCode in
/-- The error code of KeyMint. -/
abbrev KmErrorCode : Type := ErrorCode

/-- The error `e` has the root cause `error::Error::Km(ec)`. -/
def KmRoot (root : anyhow.Error → ErrRoot) (ec : KmErrorCode) (e : anyhow.Error) : Prop :=
  root e = ErrRoot.ks (error.Error.Km ec)

open core.result.Result.Insts.AnyhowContext in
open anyhow.context.ext.StdError renaming Blanket → StdBlanket in
open error.Error.Insts renaming CoreErrorError → KsErrorError in
/-- A call `Err(keystore2_error).context(format!(..))` on a result that holds a `T`. The root
cause of the new error is the keystore2 error, and an `Ok` stays `Ok`. -/
abbrev KsCtxSpec (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun x => ErrRoot.ks x) root
    (context (T := T) (StdBlanket KsErrorError) StringDisplay)

open core.result.Result.Insts.AnyhowContext in
open anyhow.context.ext.StdError renaming Blanket → StdBlanket in
open rustutils.android.system_properties.PropertyWatcherError.Insts
  renaming CoreErrorError → WatcherErrorError in
/-- A call `r.context(..)` with a `String` message on a result that holds a `T` and a property
watcher error. The new error has no class that the model knows (`ErrRoot.other`), and an `Ok`
stays `Ok`. -/
abbrev WatcherCtxSpec (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun _ => ErrRoot.other) root
    (context (T := T) (StdBlanket WatcherErrorError) StringDisplay)

/-- Assumption about `anyhow::Error::from` at a binder status code (register record
`ks2-ext-anyhow-error-insts-coreconvertfrom-from`). The call never panics and the root cause of
the error is not a class that the model knows (`ErrRoot.other`). Idealisation: allocation never
fails. -/
def StatusCodeFromSpec (root : anyhow.Error → ErrRoot) : Prop :=
  ErrorFromLaw root (fun _ => ErrRoot.other)
    (anyhowFrom statusErrorError).«from»

end Keystore2Verify.Globals
