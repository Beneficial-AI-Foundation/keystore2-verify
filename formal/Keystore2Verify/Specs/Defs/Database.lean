import Keystore2Verify.Specs.Defs.Externals
import Keystore2Verify.Specs.Defs.ExternalsMore

/-!
# Definitions for the statements about the types of `database.rs`

The statements cover the items of `database.rs` before line 1000: the metadata maps, the key
entry, `DateTime`, `BootTime`, `AuthTokenEntry` and their derived trait methods. This file holds

* the order of the variants and the lexicographic order of byte sequences, which describe what the
  derived `Ord` and `PartialOrd` return;
* new assumptions about external functions that these statements need. Each is a `Prop`. Nothing
  here is an axiom and nothing is proved.

Observations. `HashMap` is an opaque type. The view `view : HashMap → i64 → Option V` gives the
value stored under a key. The view of a `SystemTime` is the number of nanoseconds since the Unix
epoch (negative before it), and the view of a `Duration` is its number of nanoseconds. A theorem
takes a view once and passes it to every assumption it needs.
-/

open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

namespace Keystore2Verify.Database

open alloc.vec.Vec.Insts.CoreCmpOrd renaming cmp → vecCmp
open Array.Insts.CoreCmpOrd renaming cmp → arrayCmp
open core.option.Option.Insts.CoreDefaultDefault renaming default → optionDefault
open alloc.vec.Vec.Insts.CoreDefaultDefault renaming default → vecDefault
open core.option.Option.Insts.CoreCmpPartialEqOption renaming eq → optionEqFn
open std.hash.random.RandomState.Insts
  renaming CoreHashBuildHasherDefaultHasher → rsBuildHasher, CoreDefaultDefault → rsDefault
open std.hash.random
open core.borrow
open core.ops.function
open core.slice.iter
open core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT renaming any → iterAny
open std.time
open core.time
open core.time.Duration.Insts.CoreCmpPartialOrdDuration renaming partial_cmp → durationPartialCmp
open core.option
open core.num.error
open database.BlobMetaData.Insts renaming CoreCmpPartialEqBlobMetaData → blobMetaDataEqInst
open core.result.Result.Insts.AnyhowContext renaming with_context → withContext
open anyhow.context.ext
open rusqlite.error.Error.Insts renaming CoreErrorError → rusqliteErrorError
open anyhow.kind
open std.collections.hash.set
open std.sync.poison.mutex
open std.sync.poison.mutex.MutexGuard.Insts.CoreOpsDerefDerefMut
  renaming deref_mut → guardDerefMut
open alloc.vec.partial_eq.PartialEqVec renaming eq → vecPartialEq
open key_parameter.KeyParameter.Insts renaming CoreCmpPartialEqKeyParameter → keyParameterEq
open I64.Insts.CoreConvertTryFromU128TryFromIntError renaming try_from → i64TryFromU128
open U64.Insts.CoreConvertTryFromI64TryFromIntError renaming try_from → u64TryFromI64


/-! ## Variant order

The derived `PartialOrd` and `Ord` compare the variants by their position in the declaration, then
the fields of equal variants in order. -/

/-- Position of a `KeyType` variant. -/
def keyTypeRank : database.KeyType → Nat
  | .Client => 0
  | .Super => 1

/-- Position of a `KeyLifeCycle` variant. -/
def keyLifeCycleRank : database.KeyLifeCycle → Nat
  | .Existing => 0
  | .Live => 1
  | .Unreferenced => 2

/-- Position of a `BlobState` variant. -/
def blobStateRank : database.BlobState → Nat
  | .Current => 0
  | .Superseded => 1
  | .Orphaned => 2

/-- Position of an `EncryptedBy` variant. -/
def encryptedByRank : database.EncryptedBy → Nat
  | .Password => 0
  | .KeyId _ => 1

/-- Position of a `KeyMetaEntry` variant. -/
def keyMetaEntryRank : database.KeyMetaEntry → Nat
  | .CreationDate _ => 0
  | .AttestationExpirationDate _ => 1
  | .AttestationMacedPublicKey _ => 2
  | .AttestationRawPubKey _ => 3
  | .Sec1PublicKey _ => 4

/-- Position of a `BlobMetaEntry` variant. -/
def blobMetaEntryRank : database.BlobMetaEntry → Nat
  | .EncryptedBy _ => 0
  | .Salt _ => 1
  | .Iv _ => 2
  | .AeadTag _ => 3
  | .KmUuid _ => 4
  | .PublicKey _ => 5
  | .MaxBootLevel _ => 6

/-- The lexicographic order of two byte sequences (the `Ord` of `[u8]`, `Vec<u8>` and `[u8; N]`):
the first differing byte decides, and a proper prefix is smaller. -/
def lexCmp : List Std.U8 → List Std.U8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: xs, b :: ys =>
    match compare a.val b.val with
    | .eq => lexCmp xs ys
    | o => o

/-- The result of `KeyMetaEntry::cmp`: the variants are compared first, then the payloads of
equal variants. -/
def keyMetaEntryCmp : database.KeyMetaEntry → database.KeyMetaEntry → Ordering
  | .CreationDate x, .CreationDate y => compare x.val y.val
  | .AttestationExpirationDate x, .AttestationExpirationDate y => compare x.val y.val
  | .AttestationMacedPublicKey x, .AttestationMacedPublicKey y => lexCmp x.val y.val
  | .AttestationRawPubKey x, .AttestationRawPubKey y => lexCmp x.val y.val
  | .Sec1PublicKey x, .Sec1PublicKey y => lexCmp x.val y.val
  | a, b => compare (keyMetaEntryRank a) (keyMetaEntryRank b)

/-- The result of `BlobMetaEntry::cmp`: the variants are compared first, then the payloads of
equal variants. -/
def blobMetaEntryCmp : database.BlobMetaEntry → database.BlobMetaEntry → Ordering
  | .EncryptedBy x, .EncryptedBy y =>
    match x, y with
    | .KeyId i, .KeyId j => compare i.val j.val
    | a, b => compare (encryptedByRank a) (encryptedByRank b)
  | .Salt x, .Salt y => lexCmp x.val y.val
  | .Iv x, .Iv y => lexCmp x.val y.val
  | .AeadTag x, .AeadTag y => lexCmp x.val y.val
  | .KmUuid x, .KmUuid y => lexCmp x.val y.val
  | .PublicKey x, .PublicKey y => lexCmp x.val y.val
  | .MaxBootLevel x, .MaxBootLevel y => compare x.val y.val
  | a, b => compare (blobMetaEntryRank a) (blobMetaEntryRank b)

/-- The result of `EncryptedBy::cmp`. -/
def encryptedByCmp : database.EncryptedBy → database.EncryptedBy → Ordering
  | .KeyId i, .KeyId j => compare i.val j.val
  | a, b => compare (encryptedByRank a) (encryptedByRank b)

/-- The big-endian number of a list of bytes, first byte most significant. -/
def beNat (bs : List Std.U8) : Nat := leNat bs.reverse

/-! ## Assumptions about external functions

Each assumption `XAssumption` is a `Prop` over the function it models, given as a parameter.
`XSpec` is the instance at the extracted symbol. A theorem takes the `Spec`. An observation
(a view, a classifier, a time view) stays a parameter of the `Spec`. -/

/-- Assumption about the `cmp` of `Vec<u8>`: it never panics and returns the lexicographic
order. -/
def VecU8CmpAssumption (cmp : alloc.vec.Vec Std.U8 → alloc.vec.Vec Std.U8 → Result Ordering) :
    Prop :=
  ∀ a b, ∃ o, cmp a b = ok o ∧ o = lexCmp a.val b.val

/-- Assumption about `Vec<u8>::cmp` (record `ks2-ext-alloc-vec-vec-insts-corecmpord-cmp`), with
the global allocator and the order of `u8`. -/
def VecU8CmpSpec : Prop :=
  VecU8CmpAssumption (vecCmp alloc.alloc.Global core.cmp.OrdU8)

/-- Assumption about the `cmp` of `[u8; 16]`: it never panics and returns the lexicographic
order. -/
def ArrayU8Cmp16Assumption
    (cmp : Array Std.U8 16#usize → Array Std.U8 16#usize → Result Ordering) : Prop :=
  ∀ a b, ∃ o, cmp a b = ok o ∧ o = lexCmp a.val b.val

/-- Assumption about `<[u8; 16]>::cmp` (record `ks2-ext-array-insts-corecmpord-cmp`), with the
order of `u8`. -/
def ArrayU8Cmp16Spec : Prop :=
  ArrayU8Cmp16Assumption (arrayCmp core.cmp.OrdU8)

/-- Assumption about the `default` of `Option`: it never panics and returns `None`. -/
def OptionDefaultAssumption {T : Type} (default : Result (Option T)) : Prop :=
  default = ok none

/-- Assumption about `Option::default` (record
`ks2-ext-core-option-option-insts-coredefaultdefault-default`) for the type `T`. -/
def OptionDefaultSpec (T : Type) : Prop :=
  OptionDefaultAssumption (optionDefault T)

/-- Assumption about the `default` of `Vec`: it never panics and returns the empty vector. -/
def VecDefaultAssumption {T : Type} (default : Result (alloc.vec.Vec T)) : Prop :=
  ∃ v, default = ok v ∧ v.val = []

/-- Assumption about `Vec::default` (record
`ks2-ext-alloc-vec-vec-insts-coredefaultdefault-default`) for the type `T`. -/
def VecDefaultSpec (T : Type) : Prop :=
  VecDefaultAssumption (vecDefault T)

/-- Assumption about the `eq` of `Option`, for a comparison `pe` of the payloads. Two `None` are
equal, a `None` and a `Some` differ, and two `Some` are equal exactly when the payload comparison
says so (a failure of that comparison is a failure of `eq`). -/
def OptionEqAssumption {T : Type} (pe : core.cmp.PartialEq T T)
    (eq : Option T → Option T → Result Bool) : Prop :=
  (eq none none = ok true) ∧
  (∀ y, eq none (some y) = ok false) ∧
  (∀ x, eq (some x) none = ok false) ∧
  (∀ x y, eq (some x) (some y) = pe.eq x y)

/-- Assumption about `Option::eq` (record
`ks2-ext-core-option-option-insts-corecmppartialeqoption-eq`) for the comparison `pe`. -/
def OptionEqSpec {T : Type} (pe : core.cmp.PartialEq T T) : Prop :=
  OptionEqAssumption pe (optionEqFn pe)

open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open HardwareAuthToken.HardwareAuthToken.Insts.CoreCloneClone
  renaming clone → hardwareAuthTokenClone

/-- Assumption about the `clone` of a hardware auth token: it never panics and returns an equal
token. Idealisation: allocation never fails. -/
def HardwareAuthTokenCloneAssumption (clone : HardwareAuthToken.HardwareAuthToken →
    Result HardwareAuthToken.HardwareAuthToken) : Prop :=
  ∀ t, clone t = ok t

/-- The clone of a `HardwareAuthToken` never panics and returns an equal token: the shared
assumption about this external function, `ExternalsMore.HardwareAuthTokenCloneSpec`. -/
abbrev HardwareAuthTokenCloneSpec : Prop := ExternalsMore.HardwareAuthTokenCloneSpec

/-! ### `HashMap<i64, V>`

Observation: `view m k` is the value under the key `k` (`None` if there is none). Every `Spec`
below is stated at the instances the code uses: `EqI64`, `Hash` of `i64` and the random state of
the standard library. The view of a real map has a finite support. -/

section HashMap
open std.collections.hash.map
open HashMap.Insts.CoreCmpPartialEqHashMap renaming eq → hashMapEqFn
open HashMapKVSGlobal.Insts.CoreDefaultDefault renaming default → hashMapDefault

/-- A hash map from `i64` with the default hasher and the global allocator. -/
abbrev I64Map (V : Type) : Type := HashMap Std.I64 V RandomState alloc.alloc.Global

/-- A view of a map from `i64`. -/
abbrev MetaView (V : Type) : Type := I64Map V → Std.I64 → Option V

/-- `HashMap::get` at the instances of the code. -/
noncomputable abbrev hmGet {V : Type} (m : I64Map V) (k : Std.I64) : Result (Option V) :=
  HashMap.get core.cmp.EqI64 I64.Insts.CoreHashHash rsBuildHasher
    (Borrow.Blanket Std.I64) I64.Insts.CoreHashHash core.cmp.EqI64 m k

/-- `HashMap::insert` at the instances of the code. -/
noncomputable abbrev hmInsert {V : Type} (m : I64Map V) (k : Std.I64) (v : V) :
    Result (Option V × I64Map V) :=
  HashMap.insert core.cmp.EqI64 I64.Insts.CoreHashHash rsBuildHasher m k v

/-- `HashMap::eq` at the instances of the code, for a comparison `pe` of the values. -/
noncomputable abbrev hmEq {V : Type} (pe : core.cmp.PartialEq V V) (m n : I64Map V) :
    Result Bool :=
  hashMapEqFn core.cmp.EqI64 I64.Insts.CoreHashHash pe rsBuildHasher m n

/-- Assumption about the `get` of a map: it never panics and returns the value under the key. -/
def HashMapGetAssumption {V : Type} (view : MetaView V)
    (get : I64Map V → Std.I64 → Result (Option V)) : Prop :=
  ∀ m k, get m k = ok (view m k)

/-- Assumption about `HashMap::get` (record `ks2-ext-std-collections-hash-map-hashmap-get`). -/
def HashMapGetSpec {V : Type} (view : MetaView V) : Prop :=
  HashMapGetAssumption view hmGet

/-- Assumption about the `insert` of a map: `insert m k v` never panics. It returns some old value
(not observed) and a new map. In the new map `k` holds `v` and every other key is unchanged.
Idealisation: allocation never fails. -/
def HashMapInsertAssumption {V : Type} (view : MetaView V)
    (insert : I64Map V → Std.I64 → V → Result (Option V × I64Map V)) : Prop :=
  ∀ m k v, ∃ old m', insert m k v = ok (old, m') ∧ view m' k = some v ∧
    ∀ j, j ≠ k → view m' j = view m j

/-- Assumption about `HashMap::insert` (record
`ks2-ext-std-collections-hash-map-hashmap-insert`). -/
def HashMapInsertSpec {V : Type} (view : MetaView V) : Prop :=
  HashMapInsertAssumption view hmInsert

/-- Assumption about the `default` of a map: it never panics and returns the empty map.
Idealisation: allocation never fails. -/
def HashMapDefaultAssumption {V : Type} (view : MetaView V)
    (default : Result (I64Map V)) : Prop :=
  ∃ m, default = ok m ∧ ∀ k, view m k = none

/-- Assumption about `HashMap::default` (record
`ks2-ext-std-collections-hash-map-hashmapkvsglobal-insts-coredefaultdefault-default`). -/
def HashMapDefaultSpec (V : Type) (view : MetaView V) : Prop :=
  HashMapDefaultAssumption view (hashMapDefault Std.I64 V rsDefault)

/-- Assumption about the `eq` of maps, for a comparison `pe` of the values. If `pe` never fails,
then `eq` never panics, and it returns `true` exactly when the two maps have the same keys and
equal values under each key. -/
def HashMapEqAssumption {V : Type} (view : MetaView V) (pe : core.cmp.PartialEq V V)
    (eq : I64Map V → I64Map V → Result Bool) : Prop :=
  (∀ a b, ∃ r, pe.eq a b = ok r) →
  ∀ m n, ∃ r, eq m n = ok r ∧
    (r = true ↔ ∀ k, (view m k = none ∧ view n k = none) ∨
      ∃ a b, view m k = some a ∧ view n k = some b ∧ pe.eq a b = ok true)

/-- Assumption about `HashMap::eq` (record
`ks2-ext-std-collections-hash-map-hashmap-insts-corecmppartialeqhashmap-eq`) for the comparison
`pe` of the values. -/
def HashMapEqSpec {V : Type} (view : MetaView V) (pe : core.cmp.PartialEq V V) : Prop :=
  HashMapEqAssumption view pe (hmEq pe)

end HashMap

/-! ### Error context -/

/-- Assumption about the `with_context` of a `Result`. It keeps an `Ok` value. For an `Err x`,
it calls the closure to build the context. If the closure call returns, then `with_context` never
panics and returns an error `e` whose root cause is that of `x`: its class is `rootE x`.
Idealisation: allocation never fails. Idealisation: destruction never panics (the closure is a
unit closure, and is dropped on the `Ok` branch). -/
def WithContextAssumption {T E F C : Type} (rootE : E → ErrRoot) (root : anyhow.Error → ErrRoot)
    (ctx : core.result.Result T E → F → Result (core.result.Result T anyhow.Error))
    (callOnce : F → Result C) : Prop :=
  (∀ v f, ctx (.Ok v) f = ok (.Ok v)) ∧
  (∀ x f c, callOnce f = ok c → ∃ e, ctx (.Err x) f = ok (.Err e) ∧ root e = rootE x)

/-! ### Slice iterators -/

/-- Assumption about the `any` of a slice iterator, for a closure whose state is not changed.
If the closure never fails and leaves its state unchanged on every element, then `any` never
panics and returns `true` exactly when the closure returns `true` for some element that is left
in the iterator. -/
def IterAnyAssumption {T F : Type} (inst : FnMut F T Bool)
    (any : Iter T → F → Result (Bool × Iter T)) : Prop :=
  ∀ (it : Iter T) (c : F),
    (∀ x, ∃ r, inst.call_mut c x = ok (r, c)) →
    ∃ b it', any it c = ok (b, it') ∧
      (b = true ↔ ∃ x ∈ List.drop it.i it.slice.val, inst.call_mut c x = ok (true, c))

/-- Assumption about `Iter::any` on a slice iterator (record
`ks2-ext-core-slice-iter-iter-insts-coreitertraitsiteratoriteratorsharedat-any`) for the closure
`inst`. -/
def IterAnySpec {T F : Type} (inst : FnMut F T Bool) : Prop :=
  IterAnyAssumption inst (iterAny inst)

/-! ### Time

For `SystemTime` and `Duration` the views are nanoseconds. The assumptions only cover the calls
of `DateTime::now`, `DateTime::try_from` and `DateTime::try_into`. -/

/-- Assumption about `SystemTime::UNIX_EPOCH`: the constant exists and is at 0 nanoseconds. -/
def UnixEpochAssumption (nanos : SystemTime → Int) (epoch : Result SystemTime) : Prop :=
  ∃ e, epoch = ok e ∧ nanos e = 0

/-- Assumption about `SystemTime::UNIX_EPOCH` (record `ks2-ext-std-time-systemtime-unix-epoch`). -/
def UnixEpochSpec (nanos : SystemTime → Int) : Prop :=
  UnixEpochAssumption nanos SystemTime.UNIX_EPOCH

/-- Assumption about `duration_since`. `a.duration_since(b)` never panics. If `b` is not later
than `a`, it returns the `Duration` between them, and if `b` is later, it returns an error. -/
def DurationSinceAssumption (nanos : SystemTime → Int) (dnanos : Duration → Nat)
    (since : SystemTime → SystemTime →
      Result (core.result.Result Duration SystemTimeError)) : Prop :=
  ∀ a b,
    (nanos b ≤ nanos a → ∃ d, since a b = ok (.Ok d) ∧
      (dnanos d : Int) = nanos a - nanos b) ∧
    (nanos a < nanos b → ∃ e, since a b = ok (.Err e))

/-- Assumption about `SystemTime::duration_since` (record
`ks2-ext-std-time-systemtime-duration-since`). -/
def DurationSinceSpec (nanos : SystemTime → Int) (dnanos : Duration → Nat) : Prop :=
  DurationSinceAssumption nanos dnanos SystemTime.duration_since

/-- Assumption about `as_millis`: it never panics and returns the number of whole
milliseconds. -/
def DurationAsMillisAssumption (dnanos : Duration → Nat)
    (as_millis : Duration → Result Std.U128) : Prop :=
  ∀ d, ∃ m, as_millis d = ok m ∧ m.val = dnanos d / 1000000

/-- Assumption about `Duration::as_millis` (record `ks2-ext-core-time-duration-as-millis`). -/
def DurationAsMillisSpec (dnanos : Duration → Nat) : Prop :=
  DurationAsMillisAssumption dnanos Duration.as_millis

/-- Assumption about `i64::try_from(u128)`: the conversion never panics. It keeps the value if it
fits, and returns an error otherwise. -/
def I64TryFromU128Assumption
    (try_from : Std.U128 → Result (core.result.Result Std.I64 TryFromIntError)) :
    Prop :=
  ∀ m : Std.U128,
    (m.val ≤ Std.I64.max → ∃ v, try_from m = ok (.Ok v) ∧ v.val = m.val) ∧
    (Std.I64.max < m.val → ∃ e, try_from m = ok (.Err e))

/-- Assumption about `i64::try_from(u128)` (record
`ks2-ext-i64-insts-coreconverttryfromu128tryfrominterror-try-from`). -/
def I64TryFromU128Spec : Prop :=
  I64TryFromU128Assumption i64TryFromU128

/-- Assumption about `u64::try_from(i64)`: the conversion never panics. It keeps the value if it
is not negative, and returns an error otherwise. -/
def U64TryFromI64Assumption
    (try_from : Std.I64 → Result (core.result.Result Std.U64 TryFromIntError)) :
    Prop :=
  ∀ m : Std.I64,
    (0 ≤ m.val → ∃ v, try_from m = ok (.Ok v) ∧ v.val = m.val) ∧
    (m.val < 0 → ∃ e, try_from m = ok (.Err e))

/-- Assumption about `u64::try_from(i64)` (record
`ks2-ext-u64-insts-coreconverttryfromi64tryfrominterror-try-from`). -/
def U64TryFromI64Spec : Prop :=
  U64TryFromI64Assumption u64TryFromI64

/-- Assumption about `from_millis`: it never panics and returns the duration of that many
milliseconds. -/
def DurationFromMillisAssumption (dnanos : Duration → Nat)
    (from_millis : Std.U64 → Result Duration) : Prop :=
  ∀ m, ∃ d, from_millis m = ok d ∧ dnanos d = m.val * 1000000

/-- Assumption about `Duration::from_millis` (record
`ks2-ext-core-time-duration-from-millis`). -/
def DurationFromMillisSpec (dnanos : Duration → Nat) : Prop :=
  DurationFromMillisAssumption dnanos Duration.from_millis

/-- Assumption about the `partial_cmp` of `Duration`: it never panics and returns `Some` of the
order of the two durations. -/
def DurationPartialCmpAssumption (dnanos : Duration → Nat)
    (partial_cmp : Duration → Duration → Result (Option Ordering)) : Prop :=
  ∀ a b, partial_cmp a b = ok (some (compare (dnanos a) (dnanos b)))

/-- Assumption about `Duration::partial_cmp` (record
`ks2-ext-core-time-duration-insts-corecmppartialordduration-partial-cmp`). -/
def DurationPartialCmpSpec (dnanos : Duration → Nat) : Prop :=
  DurationPartialCmpAssumption dnanos durationPartialCmp

/-- Assumption about the `checked_sub` of durations: it never panics. If the second duration is
not longer than the first, it returns the difference, and otherwise it returns `None`. -/
def DurationCheckedSubAssumption (dnanos : Duration → Nat)
    (checked_sub : Duration → Duration → Result (Option Duration)) : Prop :=
  ∀ a b,
    (dnanos b ≤ dnanos a →
      ∃ d, checked_sub a b = ok (some d) ∧ dnanos d + dnanos b = dnanos a) ∧
    (dnanos a < dnanos b → checked_sub a b = ok none)

/-- Assumption about `Duration::checked_sub` (record `ks2-ext-core-time-duration-checked-sub`). -/
def DurationCheckedSubSpec (dnanos : Duration → Nat) : Prop :=
  DurationCheckedSubAssumption dnanos Duration.checked_sub

/-- Assumption about the `checked_sub` of a `SystemTime` and a `Duration`. Nothing is said about
when it returns `None`. When it returns `Some t'`, the time `t'` is the earlier one at the given
distance. -/
def SystemTimeCheckedSubAssumption (nanos : SystemTime → Int) (dnanos : Duration → Nat)
    (checked_sub : SystemTime → Duration → Result (Option SystemTime)) : Prop :=
  ∀ t d t', checked_sub t d = ok (some t') → nanos t' = nanos t - dnanos d

/-- Assumption about `SystemTime::checked_sub` (record
`ks2-ext-std-time-systemtime-checked-sub`). -/
def SystemTimeCheckedSubSpec (nanos : SystemTime → Int) (dnanos : Duration → Nat) : Prop :=
  SystemTimeCheckedSubAssumption nanos dnanos SystemTime.checked_sub

/-- Assumption about the `checked_add` of a `SystemTime` and a `Duration`. Nothing is said about
when it returns `None`. When it returns `Some t'`, the time `t'` is the later one at the given
distance. -/
def SystemTimeCheckedAddAssumption (nanos : SystemTime → Int) (dnanos : Duration → Nat)
    (checked_add : SystemTime → Duration → Result (Option SystemTime)) : Prop :=
  ∀ t d t', checked_add t d = ok (some t') → nanos t' = nanos t + dnanos d

/-- Assumption about `SystemTime::checked_add` (record
`ks2-ext-std-time-systemtime-checked-add`). -/
def SystemTimeCheckedAddSpec (nanos : SystemTime → Int) (dnanos : Duration → Nat) : Prop :=
  SystemTimeCheckedAddAssumption nanos dnanos SystemTime.checked_add

/-- Assumption about the `and_then` of `Option`, for a closure with the instance `inst`: `None`
stays `None`, and `Some x` gives the result of the closure on `x`. -/
def OptionAndThenAssumption {T U F : Type} (inst : FnOnce F T (Option U))
    (and_then : Option T → F → Result (Option U)) : Prop :=
  (∀ f, and_then none f = ok none) ∧ (∀ x f, and_then (some x) f = inst.call_once f x)

/-- Assumption about `Option::and_then` (record `ks2-ext-core-option-option-and-then`) for the
closure instance `inst`. -/
def OptionAndThenSpec {T U F : Type} (inst : FnOnce F T (Option U)) : Prop :=
  OptionAndThenAssumption inst (Option.and_then inst)

/-! ### Errors of `new_from_sql` -/

open alloc.string.String.Insts renaming CoreFmtDisplay → stringDisplay
open alloc.string.String.Insts renaming CoreFmtDebug → stringDebug

/-- `Result::with_context` at a `rusqlite` error, with a closure that builds a `String`. -/
noncomputable abbrev rusqliteWithContext {T F : Type}
    (inst : FnOnce F Unit String) :
    core.result.Result T rusqlite.error.Error → F →
      Result (core.result.Result T anyhow.Error) :=
  withContext (StdError.Blanket rusqliteErrorError) stringDisplay inst

/-- Assumption about `Result::with_context` (record
`ks2-ext-core-result-result-insts-anyhowcontext-with-context`) at `rusqliteWithContext`: it is
`WithContextAssumption` at that call. The root cause of the new error is the root cause of the
`rusqlite` error: `rootSql` classifies the root cause of a `rusqlite` error (an observation, since
a `rusqlite` error can wrap another error). -/
def RusqliteWithContextAssumption {T F : Type} (rootSql : rusqlite.error.Error → ErrRoot)
    (root : anyhow.Error → ErrRoot) (inst : FnOnce F Unit String) : Prop :=
  WithContextAssumption (T := T) rootSql root
    (rusqliteWithContext inst) (fun f => inst.call_once f ())

/-- Assumption about the `new` of `anyhow::kind::Adhoc`: `new` of a `String` message never
panics, and the error it returns has a root cause that is none of the classified types: its class
is `other`. Idealisation: allocation never fails. -/
def AnyhowAdhocNewAssumption (root : anyhow.Error → ErrRoot)
    (new : anyhow.kind.Adhoc → String → Result anyhow.Error) : Prop :=
  ∀ a s, ∃ e, new a s = ok e ∧ root e = ErrRoot.other

/-- Assumption about `anyhow::kind::Adhoc::new` (record `ks2-ext-anyhow-kind-adhoc-new`) at
`String`. -/
def AnyhowAdhocNewSpec (root : anyhow.Error → ErrRoot) : Prop :=
  AnyhowAdhocNewAssumption root (Adhoc.new stringDisplay stringDebug)

/-- Assumption about `anyhow::__private::must_use`: the call never panics and returns its
argument. -/
def AnyhowMustUseAssumption (must_use : anyhow.Error → Result anyhow.Error) : Prop :=
  ∀ e, must_use e = ok e

/-- `anyhow::__private::must_use` never panics and returns its argument: the shared assumption about
this external function, `ExternalsMore.AnyhowMustUseSpec`. -/
abbrev AnyhowMustUseSpec : Prop := ExternalsMore.AnyhowMustUseSpec

/-! ### Locked keys and parameters -/

/-- The set of locked key ids. -/
abbrev KeySet : Type :=
  HashSet Std.I64 RandomState alloc.alloc.Global

/-- A guard of the mutex around the set of locked key ids. -/
abbrev KeySetGuard : Type := MutexGuard KeySet

/-- `Mutex::lock` on the set of locked key ids. -/
noncomputable abbrev keySetLock (m : Mutex KeySet) :=
  Mutex.lock m

/-- `MutexGuard::deref_mut` on the guard of the set of locked key ids. -/
noncomputable abbrev keySetDerefMut (g : KeySetGuard) :=
  guardDerefMut g

/-- `HashSet::insert` on the set of locked key ids. -/
noncomputable abbrev keySetInsert (hs : KeySet) (k : Std.I64) :=
  HashSet.insert core.cmp.EqI64 I64.Insts.CoreHashHash
    rsBuildHasher hs k

/-- The comparison of two vectors of key parameters, as `Vec::eq` at the derived `eq` of
`KeyParameter`. -/
noncomputable abbrev keyParametersEq (a b : alloc.vec.Vec key_parameter.KeyParameter) :=
  vecPartialEq
    keyParameterEq a b

/-- The comparison of two optional key blobs (a blob and its metadata), as `Option::eq` at the
derived `eq` of the pair. -/
noncomputable abbrev blobInfoEq (a b : Option (alloc.vec.Vec Std.U8 × database.BlobMetaData)) :=
  optionEqFn (Pair.Insts.CoreCmpPartialEqPair (core.cmp.PartialEqVec core.cmp.PartialEqU8)
    blobMetaDataEqInst) a b

end Keystore2Verify.Database
