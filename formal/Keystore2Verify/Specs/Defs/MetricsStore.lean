import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `metrics_store.rs`

Value tables of the bitmap functions, the arithmetic of the two rounding functions, and the new
assumptions about external functions that the statements need. Nothing here is an axiom.

An assumption is a `Prop` that a theorem takes as an explicit hypothesis. The shared observations
are the views `entries` and `seqOf` of a hash map and of its iterator, and the classifier `root`
of `Externals.lean`. Idealisation for every assumption of this file: allocation never fails.
-/

namespace Keystore2Verify.MetricsStore
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2.core.num.U64 renaming ilog10 → u64Ilog10, pow → u64Pow
open keystore2.core.num.U32 renaming ilog10 → u32Ilog10, pow → u32Pow
open keystore2.core.time.Duration renaming as_millis → durationAsMillis
open anyhow.error.Error renaming msg → anyhowMsg
open alloc.string.String.Insts renaming CoreFmtDisplay → stringDisplay, CoreFmtDebug → stringDebug
open std.collections.hash.map
open std.hash.random
open Aeneas.Std.core.iter.adapters.map
open keystore2.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
  renaming next → mapNext
open keystore2.core.iter.traits.iterator.Iterator.map renaming default → iteratorMapDefault
open keystore2.core.option.Option renaming map_or → optionMapOr
open Aeneas.Std.core.borrow.Borrow renaming Blanket → borrowBlanket

/-! ## Value tables -/

/-- The bit that `compute_padding_mode_bitmap` sets for a padding mode number: `none` for a number
that is not listed. The numbers are the AIDL values of `PaddingMode` (NONE 1, RSA_OAEP 2,
RSA_PSS 3, RSA_PKCS1_1_5_ENCRYPT 4, RSA_PKCS1_1_5_SIGN 5, PKCS7 64). -/
def paddingBitPos : Int → Option Nat
  | 1 => some 0
  | 2 => some 1
  | 3 => some 2
  | 4 => some 3
  | 5 => some 4
  | 64 => some 5
  | _ => none

/-- The bit that `compute_digest_bitmap` sets for a digest number (NONE 0, MD5 1, SHA1 2,
SHA_2_224 3, SHA_2_256 4, SHA_2_384 5, SHA_2_512 6). -/
def digestBitPos : Int → Option Nat
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | 4 => some 4
  | 5 => some 5
  | 6 => some 6
  | _ => none

/-- The bit that `compute_block_mode_bitmap` sets for a block mode number (ECB 1, CBC 2, CTR 3,
GCM 32). -/
def blockModeBitPos : Int → Option Nat
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | 32 => some 4
  | _ => none

/-- The bit that `compute_purpose_bitmap` sets for a key purpose number (ENCRYPT 0, DECRYPT 1,
SIGN 2, VERIFY 3, WRAP_KEY 5, AGREE_KEY 6, ATTEST_KEY 7). -/
def purposeBitPos : Int → Option Nat
  | 0 => some 1
  | 1 => some 2
  | 2 => some 3
  | 3 => some 4
  | 5 => some 5
  | 6 => some 6
  | 7 => some 7
  | _ => none

/-- The atom numbers that `get_atoms` reads from the stored map. -/
def storedAtomIds : List Int :=
  [10118, 10119, 10120, 10121, 10122, 10123, 10124, 10267, 10268, 10270, 10271]

/-- The atom numbers that `get_atoms` computes when it is called, and does not read from the
map: `STORAGE_STATS`, `KEYS_PER_UID` and `CRASH_STATS`. -/
def computedAtomIds : List Int := [10103, 10248, 10125]

/-! ## Arithmetic of the two rounding functions -/

/-- The step of `round_logarithmic` for `val > 0`: `10^(e+1) / buckets_per_decade` with
`e = ⌊log₁₀ val⌋`, at least `min_step`. -/
def roundLogStep (val buckets minStep : Nat) : Nat :=
  max (10 ^ (Nat.log 10 val + 1) / buckets) minStep

/-- The value before the final cap in `round_logarithmic`: `val` rounded to the nearest multiple
of the step, halves rounding up. -/
def roundLogRounded (val buckets minStep : Nat) : Nat :=
  (val + roundLogStep val buckets minStep / 2) / roundLogStep val buckets minStep *
    roundLogStep val buckets minStep

/-- The step of `round_latency` for a millisecond count `ms` (already capped): 5 up to 10 ms, 10
up to 100 ms, and half the largest power of ten at most `ms` above that. -/
def latencyStep (ms : Nat) : Nat :=
  if ms ≤ 10 then 5 else if ms ≤ 100 then 10 else 10 ^ Nat.log 10 ms / 2

/-- The result of `round_latency` for a duration of `n` whole milliseconds: `n` is capped at
`i32::MAX`, then rounded to the nearest multiple of the step, halves rounding up. -/
def roundLatencyNat (n : Nat) : Nat :=
  let ms := min n (2 ^ 31 - 1)
  (ms + latencyStep ms / 2) / latencyStep ms * latencyStep ms

/-- The count that `update_keystore_crash_sysprop` writes: the stored count plus one, or 0 if the
property is absent. -/
def crashCountNext : Option Std.I32 → Result Std.I32
  | none => ok 0#i32
  | some c => c + 1#i32

/-! ## Assumptions about external functions

Each assumption is a `Prop` over the function as a parameter. The closed `...Spec` instance
applies it to the extracted symbol. The power assumptions cover base 10 and the exponents that
the callers reach. -/

/-- Assumption about an external function `ilog10` on `u64`: for a positive argument it returns
`⌊log₁₀ v⌋` and does not panic. Nothing is assumed for 0, where Rust panics. -/
def U64Ilog10Assumption (ilog10 : Std.U64 → Result Std.U32) : Prop :=
  ∀ v : Std.U64, 0 < v.val → ∃ e, ilog10 v = ok e ∧ e.val = Nat.log 10 v.val

/-- Closed instance of `U64Ilog10Assumption` for `u64::ilog10` (record id
`ks2-ext-core-num-u64-ilog10`). -/
def U64Ilog10Spec : Prop := U64Ilog10Assumption u64Ilog10

/-- Assumption about an external function `pow` on `u64`, for base 10 and the exponents 1 to 20
(the exponents `round_logarithmic` reaches). If `10^e` fits in a `u64` the call returns it. If it
does not fit, the call panics (`fail`). Target assumption: the second part holds for builds with
overflow checks, as Android builds are. -/
def U64PowTenAssumption (pow : Std.U64 → Std.U32 → Result Std.U64) : Prop :=
  ∀ e : Std.U32, 1 ≤ e.val → e.val ≤ 20 →
    (10 ^ e.val < 2 ^ 64 → ∃ r, pow 10#u64 e = ok r ∧ r.val = 10 ^ e.val) ∧
    (2 ^ 64 ≤ 10 ^ e.val → ∃ x, pow 10#u64 e = fail x)

/-- Closed instance of `U64PowTenAssumption` for `u64::pow` (record id
`ks2-ext-core-num-u64-pow`). -/
def U64PowSpec : Prop := U64PowTenAssumption u64Pow

/-- Assumption about an external function `ilog10` on `u32`: for an argument of at least 101 (the
values that `round_latency` passes) it returns `⌊log₁₀ v⌋` and does not panic. -/
def U32Ilog10Assumption (ilog10 : Std.U32 → Result Std.U32) : Prop :=
  ∀ v : Std.U32, 101 ≤ v.val → ∃ e, ilog10 v = ok e ∧ e.val = Nat.log 10 v.val

/-- Closed instance of `U32Ilog10Assumption` for `u32::ilog10` (record id
`ks2-ext-core-num-u32-ilog10`). -/
def U32Ilog10Spec : Prop := U32Ilog10Assumption u32Ilog10

/-- Assumption about an external function `pow` on `u32`, for base 10 and the exponents 2 to 9
(the exponents `round_latency` reaches). The call returns `10^e` and does not panic. -/
def U32PowTenAssumption (pow : Std.U32 → Std.U32 → Result Std.U32) : Prop :=
  ∀ e : Std.U32, 2 ≤ e.val → e.val ≤ 9 → ∃ r, pow 10#u32 e = ok r ∧ r.val = 10 ^ e.val

/-- Closed instance of `U32PowTenAssumption` for `u32::pow` (record id
`ks2-ext-core-num-u32-pow`). -/
def U32PowSpec : Prop := U32PowTenAssumption u32Pow

/-- Assumption about an external function `as_millis`, over the observation `millis` of a
duration as a whole number of milliseconds. The call does not panic and returns that number. -/
def DurationAsMillisAssumption (millis : core.time.Duration → Nat)
    (as_millis : core.time.Duration → Result Std.U128) : Prop :=
  ∀ d, ∃ m, as_millis d = ok m ∧ m.val = millis d

/-- Closed instance of `DurationAsMillisAssumption` for `Duration::as_millis` (record id
`ks2-ext-core-time-duration-as-millis`). -/
def DurationAsMillisSpec (millis : core.time.Duration → Nat) : Prop :=
  DurationAsMillisAssumption millis durationAsMillis

/-- Assumption about an external function `format_err`: it never panics. The error it returns
comes from a message, so its root cause is not one of the error types that `root` names: the
class is `other`. -/
def AnyhowFormatErrAssumption (root : anyhow.Error → ErrRoot)
    (format_err : core.fmt.Arguments → Result anyhow.Error) : Prop :=
  ∀ a, ∃ e, format_err a = ok e ∧ root e = ErrRoot.other

/-- Closed instance of `AnyhowFormatErrAssumption` for `anyhow::__private::format_err` (record id
`ks2-ext-anyhow-private-format-err`). -/
def AnyhowFormatErrSpec (root : anyhow.Error → ErrRoot) : Prop :=
  AnyhowFormatErrAssumption root anyhow.__private.format_err

/-- Assumption about an external function `must_use` on errors: it never panics and the error it
returns has the same class under `root` as its argument. -/
def AnyhowMustUseAssumption (root : anyhow.Error → ErrRoot)
    (must_use : anyhow.Error → Result anyhow.Error) : Prop :=
  ∀ e, ∃ e', must_use e = ok e' ∧ root e' = root e

/-- Closed instance of `AnyhowMustUseAssumption` for `anyhow::__private::must_use` (record id
`ks2-ext-anyhow-private-must-use`). -/
def AnyhowMustUseSpec (root : anyhow.Error → ErrRoot) : Prop :=
  AnyhowMustUseAssumption root anyhow.__private.must_use

/-- Assumption about an external function `Error::msg` for a `String` message: it never panics.
The error it returns comes from a message, so its class under `root` is `other`. -/
def AnyhowErrorMsgAssumption (root : anyhow.Error → ErrRoot)
    (msg : String → Result anyhow.Error) : Prop :=
  ∀ s, ∃ e, msg s = ok e ∧ root e = ErrRoot.other

/-- Closed instance of `AnyhowErrorMsgAssumption` for `anyhow::Error::msg` at `String` (record id
`ks2-ext-anyhow-error-error-msg`). -/
def AnyhowErrorMsgStringSpec (root : anyhow.Error → ErrRoot) : Prop :=
  AnyhowErrorMsgAssumption root (anyhowMsg stringDisplay stringDebug)

/-! ## The map of counted atoms

`get_atoms` reads the inner map of one atom number through `HashMap::iter`, `Iterator::map` and
`collect`. The observation `entries` lists the pairs of an inner map in the order in which its
iterator yields them, and `seqOf` lists the pairs that an iterator has still to yield. -/

section AtomMaps

open android_security_metrics.aidl.android.security.metrics
open KeystoreAtomPayload.KeystoreAtomPayload.Insts.CoreCloneClone renaming clone → payloadClone
open metrics_store.MetricsStore.get_atoms.closure.closure.Insts renaming
  CoreOpsFunctionFnMutTuplePairShared0KeystoreAtomPayloadShared1I32KeystoreAtom →
    atomClosureFnMut
open Iter.Insts renaming
  CoreIterTraitsIteratorIteratorPairSharedAKSharedAV → atomIterInst

/-- The key type of an inner map: an atom payload. -/
abbrev AtomPayload : Type := KeystoreAtomPayload.KeystoreAtomPayload

/-- An atom with its count. -/
abbrev Atom : Type := KeystoreAtom.KeystoreAtom

/-- The inner map type: payloads with their counts. -/
abbrev AtomMap : Type :=
  HashMap AtomPayload Std.I32 RandomState
    alloc.alloc.Global

/-- The iterator type of an inner map. -/
abbrev AtomIter : Type := Iter AtomPayload Std.I32

/-- Assumption about an external function `HashMap::iter` on an inner map. It never panics. The
iterator it returns yields the pairs `entries m`, once each, in this order. -/
def HashMapIterAssumption (entries : AtomMap → List (AtomPayload × Std.I32))
    (seqOf : AtomIter → List (AtomPayload × Std.I32))
    (iter : AtomMap → Result AtomIter) : Prop :=
  ∀ m, ∃ it, iter m = ok it ∧ seqOf it = entries m

/-- Closed instance of `HashMapIterAssumption` for `HashMap::iter` (record id
`ks2-ext-std-collections-hash-map-hashmap-iter`). -/
def HashMapIterSpec (entries : AtomMap → List (AtomPayload × Std.I32))
    (seqOf : AtomIter → List (AtomPayload × Std.I32)) : Prop :=
  HashMapIterAssumption entries seqOf HashMap.iter

/-- Assumption about an external function `Iterator::map` at the iterator of an inner map and the
closure of `get_atoms`. It never panics and pairs the iterator with the closure. -/
def IteratorMapAssumption
    (map : AtomIter → Unit → Result (Map AtomIter Unit)) : Prop :=
  ∀ it : AtomIter, map it () = ok ⟨it, ()⟩

/-- Closed instance of `IteratorMapAssumption` for `Iterator::map` (record id
`ks2-ext-core-iter-traits-iterator-iterator-map-default`). -/
def IteratorMapSpec : Prop :=
  IteratorMapAssumption
    (iteratorMapDefault (atomIterInst AtomPayload Std.I32)
      atomClosureFnMut)

/-- Assumption about an external function `Map::next` at the iterator of an inner map and the
closure of `get_atoms`. If the iterator has nothing left, `next` returns `none`. Otherwise, if the
closure gives `a` for the next pair `p`, `next` returns `a` and the iterator that has the rest
still to yield. -/
def MapNextAssumption (seqOf : AtomIter → List (AtomPayload × Std.I32))
    (next : Map AtomIter Unit →
      Result (Option Atom × Map AtomIter Unit)) : Prop :=
  ∀ it : AtomIter,
    (seqOf it = [] → ∃ it', next ⟨it, ()⟩ = ok (none, ⟨it', ()⟩)) ∧
    (∀ p rest a, seqOf it = p :: rest → atomClosureFnMut.call_mut () p = ok (a, ()) →
      ∃ it', next ⟨it, ()⟩ = ok (some a, ⟨it', ()⟩) ∧ seqOf it' = rest)

/-- Closed instance of `MapNextAssumption` for `Map::next` (record id
`ks2-ext-core-iter-adapters-map-map-insts-coreitertraitsiteratoriterator-next`). -/
def MapNextSpec (seqOf : AtomIter → List (AtomPayload × Std.I32)) : Prop :=
  MapNextAssumption seqOf
    (mapNext
      (atomIterInst AtomPayload Std.I32) atomClosureFnMut)

/-- Assumption about an external function `clone` on an atom payload: it never panics and returns
an equal value. -/
def AtomPayloadCloneAssumption (clone : AtomPayload → Result AtomPayload) : Prop :=
  ∀ p, clone p = ok p

/-- Closed instance of `AtomPayloadCloneAssumption` for `KeystoreAtomPayload::clone` (record id
below, no line break possible):
`ks2-ext-android-security-metrics-aidl-android-security-metrics-keystoreatompayload-keystoreatompayload-insts-corecloneclone-clone`. -/
def AtomPayloadCloneSpec : Prop :=
  AtomPayloadCloneAssumption payloadClone

open metrics_store.MetricsStore.get_atoms.closure.Insts renaming
  CoreOpsFunctionFnOnceTupleShared0HashMapKeystoreAtomPayloadI32RandomStateGlobalResultVecKeystoreAtomError
    → mapClosureFnOnce

/-- Assumption about an external function `Option::map_or`, for a closure whose call is
`call_once`. For `None` it returns the default value. For `Some x` it returns what the closure
gives for `x`. The call itself does not panic. Idealisation: destruction never panics (the value
that is not used is dropped). -/
def OptionMapOrAssumption {T U F : Type} (call_once : F → T → Result U)
    (map_or : Option T → U → F → Result U) : Prop :=
  (∀ d f, map_or none d f = ok d) ∧ (∀ x d f, map_or (some x) d f = call_once f x)

/-- Closed instance of `OptionMapOrAssumption` for `Option::map_or` at the closure that
`get_atoms` passes (record id `ks2-ext-core-option-option-map-or`). -/
def OptionMapOrSpec : Prop :=
  OptionMapOrAssumption mapClosureFnOnce.call_once (optionMapOr mapClosureFnOnce)

/-- The type of the outer map of the store: atom numbers with their inner maps. -/
abbrev AtomStore : Type :=
  HashMap Std.I32 AtomMap RandomState
    alloc.alloc.Global

open RandomState.Insts renaming
  CoreHashBuildHasherDefaultHasher → buildHasher in
open AtomID.AtomID.Insts renaming CoreCmpEq → atomIdEq, CoreHashHash → atomIdHash in
/-- The call of `HashMap::get` on the outer map, with the instances that `get_atoms` passes. -/
noncomputable abbrev getAtom (hm : AtomStore) (atom_id : Std.I32) : Result (Option AtomMap) :=
  HashMap.get atomIdEq atomIdHash buildHasher
    (borrowBlanket Std.I32) atomIdHash atomIdEq hm atom_id

end AtomMaps

end Keystore2Verify.MetricsStore
