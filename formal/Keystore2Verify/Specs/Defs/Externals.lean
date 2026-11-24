import Keystore2Verify.Extraction.Keystore2

/-!
# Laws about external functions

The translation of keystore2 declares some functions only by their type (an `axiom`). Lean knows
nothing about what such a function returns. This file states what we assume about them. It
contains definitions only: nothing here is an axiom and nothing is proved.

Each law is a `Prop` about one external function, written over that function as a parameter.
A theorem about keystore2 takes the laws it needs as explicit hypotheses.

* A law that needs a shared observation of an opaque type takes it as a parameter: a view
  `VecDeque → List` for the queue, a classifier `root` for `anyhow::Error`. Such a law has no
  closed instance.
* A law that needs no observation also has a closed instance for the real axiom, named `...Spec`.

Every law holds for the real Rust function, with these labels:

* **idealisation: allocation never fails.** The real process aborts when memory runs out. A law
  with this label says the call does not fail.
* **idealisation: formatting never panics.** No `Display` or `Debug` implementation reached by
  the verified code returns an error or panics, and no writer panics. The laws are stated for
  every implementation and every writer, which is stronger than the real library.
* **idealisation: destruction never panics.** Dropping an element does not panic.
* **idealisation: logging never panics.** Effects of logging are not modelled.
* **target assumption.** The law depends on the target machine.

A Lean value has the form `Result (core.result.Result T E)`. The outer layer `fail` is a Rust
panic. The inner layer `Err` is a Rust error. Each law says what it means for each layer.
-/

open Aeneas Aeneas.Std Result keystore2

namespace Keystore2Verify.Externals

/-! Short names for the axioms below, so that no identifier has more than two dots. -/

open keystore2.android_hardware_security_keymint.aidl.android.hardware.security.keymint
open EcCurve.EcCurve.Insts.CoreFmtDebug renaming fmt → ecCurveDebugFmt
open KeyFormat.KeyFormat.Insts.CoreFmtDebug renaming fmt → keyFormatDebugFmt
open KeyParameterValue.KeyParameterValue.Insts.CoreFmtDebug renaming fmt → keyParameterValueDebugFmt
open keystore2.android_system_keystore2.aidl.android.system.keystore2
open Domain.Domain.Insts.CoreFmtDebug renaming fmt → domainDebugFmt
open keystore2.core.fmt.Arguments renaming from_str_nonconst → argumentsFromStr
open keystore2.Shared0T.Insts.CoreFmtDisplay renaming fmt → shared0TDisplayFmt
open keystore2.Mut0T.Insts.CoreFmtDisplay renaming fmt → mut0TDisplayFmt
open keystore2.Str.Insts.CoreFmtDisplay renaming fmt → strDisplayFmt
open keystore2.alloc.string.String.Insts.CoreFmtDisplay renaming fmt → stringDisplayFmt
open keystore2.log.Level.Insts.CoreCmpPartialOrdLevelFilter renaming partial_cmp → levelPartialCmp
open keystore2.core.panic.location renaming Location → LogLocation
open keystore2.log.__private_api.GlobalLogger.Insts renaming LogLog → globalLoggerLog
open keystore2.core.num.U32 renaming from_ne_bytes → u32FromNeBytes
open keystore2.core.num.I32 renaming from_ne_bytes → i32FromNeBytes
open keystore2.core.num.I64 renaming from_ne_bytes → i64FromNeBytes
open keystore2.core.slice.Slice renaming first → sliceFirst
open keystore2.alloc.vec.Vec renaming truncate → vecTruncate
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming ne → sliceVecNe
open keystore2.keystore2_crypto.zvec.ZVec.Insts.CoreOpsDerefDerefSliceU8 renaming
  deref → zvecDeref
open keystore2.keystore2_selinux.Context.Insts.CoreOpsDerefDerefCStr renaming
  deref → contextDeref

/-! ## Shapes shared by several laws -/

/-- The function never panics, and always returns a value. Nothing is said about the value. -/
def TotalLaw {A B : Type} (f : A → Result B) : Prop :=
  ∀ a, ∃ b, f a = ok b

/-- Same as `TotalLaw`, for a function of two arguments. -/
def Total2Law {A B C : Type} (f : A → B → Result C) : Prop :=
  ∀ a b, ∃ c, f a b = ok c

/-! ## anyhow

Observation: `anyhow::Error` is an opaque type. Callers look at an error only through its root
cause (`keystore2/src/error.rs`: `e.root_cause().downcast_ref::<Error>()`). The classifier
`root` gives the type of the root cause. The laws say nothing about messages, backtraces or
equality of errors. Source: `anyhow` 1.0.102, `src/error.rs` and `src/context.rs`.
-/

/-- The root-cause class of an `anyhow::Error`. One constructor for each error type that keystore2
code downcasts to and that the four verified files wrap. All other types are `other`. -/
inductive ErrRoot where
  /-- `keystore2::error::Error` -/
  | ks (e : error.Error)
  /-- `keystore2_selinux::Error` -/
  | selinux (e : keystore2_selinux.Error)
  /-- `keystore2_crypto::error::Error` -/
  | crypto (e : keystore2_crypto.error.Error)
  /-- any other error type -/
  | other

/-- Law for `anyhow::Error::new` (register record `ks2-ext-anyhow-error-error-new`).
`new x` never panics, and the error it returns has the root cause `x`. The class of `x` is
`wrap x`: use `ErrRoot.ks`, `ErrRoot.selinux` or `ErrRoot.crypto` for the three wrapped types.
Idealisation: allocation never fails. Source: `anyhow` `Error::new` and `Error::from_std`.
It holds for these types because none of them has a `source`: for the variants that wrap
another error, `#[error(transparent)]` hands `source` on to a type without one. -/
def ErrorNewLaw {Err E : Type} (root : Err → ErrRoot) (wrap : E → ErrRoot)
    (new : E → Result Err) : Prop :=
  ∀ x, ∃ e, new x = ok e ∧ root e = wrap x

/-- Law for `From<E> for anyhow::Error` (register record
`ks2-ext-anyhow-error-insts-coreconvertfrom-from`).
Same content as `ErrorNewLaw`: `from x` never panics and the root cause is `x`.
Idealisation: allocation never fails. Source: `anyhow` `impl From<E> for Error`, which calls
`Error::from_std`. -/
def ErrorFromLaw {Err E : Type} (root : Err → ErrRoot) (wrap : E → ErrRoot)
    (from_ : E → Result Err) : Prop :=
  ∀ x, ∃ e, from_ x = ok e ∧ root e = wrap x

/-- Law for `anyhow::Error::context` (register record `ks2-ext-anyhow-error-error-context`).
`context e c` never panics. The new error has the same root cause as `e`.
Idealisation: allocation never fails. Source: `anyhow` `Error::context`, which wraps the
error in a `ContextError` whose `source` is `e`. -/
def ErrorContextLaw {Err C : Type} (root : Err → ErrRoot)
    (context : Err → C → Result Err) : Prop :=
  ∀ e c, ∃ e', context e c = ok e' ∧ root e' = root e

/-- Law for `StdError::ext_context` on `anyhow::Error` (register record
`ks2-ext-anyhow-error-insts-anyhowcontextextstderror-ext-context`).
`ext_context e c` never panics. The new error has the same root cause as `e`.
Idealisation: allocation never fails. Source: `anyhow` `src/context.rs`, where this method
calls `Error::context`. -/
def ExtContextErrorLaw {Err C : Type} (root : Err → ErrRoot)
    (ext_context : Err → C → Result Err) : Prop :=
  ∀ e c, ∃ e', ext_context e c = ok e' ∧ root e' = root e

/-- Law for `StdError::ext_context` on a standard error type (register record
`ks2-ext-anyhow-context-ext-stderror-blanket-ext-context`).
`ext_context x c` never panics. The new error has the root cause `x`, of class `wrap x`.
Idealisation: allocation never fails. Source: `anyhow` `src/context.rs`, where this method
calls `Error::from_context`. -/
def ExtContextBlanketLaw {Err E C : Type} (root : Err → ErrRoot) (wrap : E → ErrRoot)
    (ext_context : E → C → Result Err) : Prop :=
  ∀ x c, ∃ e, ext_context x c = ok e ∧ root e = wrap x

/-- Law for `anyhow::Context::context` on a `Result` (register record
`ks2-ext-core-result-result-insts-anyhowcontext-context`).
The call never panics. An `Ok v` stays `Ok v`. An `Err x` becomes an `Err e` whose class is
`rootE x`: `rootE` is `root` when the input error is an `anyhow::Error`, and `wrap` when it is a
wrapped standard error type.
Idealisation: allocation never fails. Source: `anyhow` `src/context.rs`, `impl Context for
Result`. -/
def ResultContextLaw {T E Err C : Type} (rootE : E → ErrRoot) (root : Err → ErrRoot)
    (context : core.result.Result T E → C → Result (core.result.Result T Err)) : Prop :=
  (∀ v c, context (.Ok v) c = ok (.Ok v)) ∧
  (∀ x c, ∃ e, context (.Err x) c = ok (.Err e) ∧ root e = rootE x)

/-! ## Formatting

Used by the `ks_err!` and `bloberr!` macros and by `format!`. The laws say that the calls do not
panic. The text is out of scope. Source: Rust standard library documentation.

Every law of this group except `from_str_nonconst` carries the label **idealisation: formatting
never panics**. Real `format` panics when a `Display` or `Debug` implementation returns an error
or panics, and a `fmt` call panics when its writer panics. The laws hold for every argument and
every formatter, so they say more than the library does. They are true of the code under
verification, where all implementations are derived or are those of integers, `str`, `String`
and the error types, and the writer is a `String`. -/

/-- Law for `alloc::fmt::format` (register record `ks2-ext-alloc-fmt-format`).
`format a` never panics.
Idealisation: formatting never panics (see the group comment), and allocation never fails. -/
def AllocFmtFormatSpec : Prop := TotalLaw alloc.fmt.format

/-- Law for `core::fmt::Arguments::from_str_nonconst` (register record
`ks2-ext-core-fmt-arguments-from-str-nonconst`).
`from_str_nonconst s` never panics. It builds a value on the stack and does not allocate. -/
def CoreFmtArgumentsFromStrNonconstSpec : Prop := TotalLaw argumentsFromStr

/-- Law for `Display` of a reference `&T` (register record
`ks2-ext-shared0t-insts-corefmtdisplay-fmt`).
If `fmt` of `T` never panics, then `fmt` of `&T` never panics. The inner layer (`fmt::Error`)
is left open.
Idealisation: formatting never panics. Source: `core::fmt`, which forwards to `T`. -/
def Shared0TDisplayFmtSpec : Prop :=
  ∀ {T : Type} (D : core.fmt.Display T),
    Total2Law D.fmt → Total2Law (shared0TDisplayFmt D)

/-- Law for `Display` of a mutable reference `&mut T` (register record
`ks2-ext-mut0t-insts-corefmtdisplay-fmt`).
If `fmt` of `T` never panics, then `fmt` of `&mut T` never panics. The inner layer is left
open.
Idealisation: formatting never panics. Source: `core::fmt`, which forwards to `T`. -/
def Mut0TDisplayFmtSpec : Prop :=
  ∀ {T : Type} (D : core.fmt.Display T),
    Total2Law D.fmt → Total2Law (mut0TDisplayFmt D)

/-- Law for `Display` of `str` (register record `ks2-ext-str-insts-corefmtdisplay-fmt`).
`fmt` never panics. The inner layer is left open. Idealisation: formatting never panics. -/
def StrDisplayFmtSpec : Prop := Total2Law strDisplayFmt

/-- Law for `Display` of `String` (register record
`ks2-ext-alloc-string-string-insts-corefmtdisplay-fmt`).
`fmt` never panics. The inner layer is left open. Idealisation: formatting never panics. -/
def StringDisplayFmtSpec : Prop := Total2Law stringDisplayFmt

/-- Law for `Debug` of `EcCurve` (register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-eccurve-eccurve-insts-corefmtdebug-fmt`).
`fmt` never panics. The inner layer is left open.
Idealisation: formatting never panics. Source: derived `Debug` of an AIDL enum. -/
def EcCurveDebugFmtSpec : Prop := Total2Law ecCurveDebugFmt

/-- Law for `Debug` of `KeyFormat` (register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-keyformat-keyformat-insts-corefmtdebug-fmt`).
`fmt` never panics. The inner layer is left open.
Idealisation: formatting never panics. Source: derived `Debug` of an AIDL enum. -/
def KeyFormatDebugFmtSpec : Prop := Total2Law keyFormatDebugFmt

/-- Law for `Debug` of `KeyParameterValue` (register record
`ks2-ext-android-hardware-security-keymint-aidl-android-hardware-security-keymint-keyparametervalue-keyparametervalue-insts-corefmtdebug-fmt`).
`fmt` never panics. The inner layer is left open.
Idealisation: formatting never panics. Source: derived `Debug` of an AIDL union. -/
def KeyParameterValueDebugFmtSpec : Prop := Total2Law keyParameterValueDebugFmt

/-- Law for `Debug` of `Domain` (register record
`ks2-ext-android-system-keystore2-aidl-android-system-keystore2-domain-domain-insts-corefmtdebug-fmt`).
`fmt` never panics. The inner layer is left open.
Idealisation: formatting never panics. Source: derived `Debug` of an AIDL enum. -/
def DomainDebugFmtSpec : Prop := Total2Law domainDebugFmt

/-! ## log

The `log::error!` and `log::warn!` expansions. Idealisation for every law of this group: a
logging call never panics. Effects (the text written to the log, the current maximum level) are
not modelled, and two calls are not compared. Source: `log` 0.4.29, `src/lib.rs` and
`src/__private_api.rs`. -/

/-- Law for `log::max_level` (register record `ks2-ext-log-max-level`).
The call returns a level and does not panic. Which level is not stated: it is the current
setting of the logger. Idealisation: logging never panics; effects are not modelled. -/
def LogMaxLevelSpec : Prop := ∃ l, log.max_level = ok l

/-- Law for the comparison of `Level` with `LevelFilter` (register record
`ks2-ext-log-level-insts-corecmppartialordlevelfilter-partial-cmp`).
`partial_cmp` never panics. The order itself is not stated. Idealisation: logging never panics;
effects are not modelled. -/
def LogLevelPartialCmpSpec : Prop :=
  Total2Law levelPartialCmp

/-- Law for `log::__private_api::loc` (register record `ks2-ext-log-private-api-loc`).
The call returns a location and does not panic. Idealisation: logging never panics;
effects are not modelled. -/
def LogLocSpec : Prop := ∃ l, log.__private_api.loc = ok l

/-- Law for `log::__private_api::log` (register record `ks2-ext-log-private-api-log`).
For the global logger and no key-value pairs, which is what the macros use, the call returns
`()` and does not panic. Idealisation: logging never panics; effects are not modelled. -/
def LogPrivateApiLogSpec : Prop :=
  ∀ (l : log.__private_api.GlobalLogger) (a : core.fmt.Arguments) (lv : log.Level)
    (t : Str × Str × LogLocation),
    log.__private_api.log Tuple.Insts.Log__private_apiSealedKVs
      globalLoggerLog l a lv t () = ok ()

/-! ## VecDeque

Observation: `VecDeque T A` is an opaque type. The view `view : Q → List T` gives the elements,
front of the queue first. Source: Rust standard library documentation of
`alloc::collections::VecDeque`. A theorem takes the view `view` once and passes it to every law. -/

/-- Law for `VecDeque::new` (register record
`ks2-ext-alloc-collections-vec-deque-vecdequetglobal-new`).
`new` never panics, and the queue it returns is empty. `new` does not allocate. -/
def VecDequeNewLaw {Q T : Type} (view : Q → List T) (new : Result Q) : Prop :=
  ∃ q, new = ok q ∧ view q = []

/-- Law for `VecDeque::len` (register record `ks2-ext-alloc-collections-vec-deque-vecdeque-len`).
`len` never panics and returns the number of elements. -/
def VecDequeLenLaw {Q T : Type} (view : Q → List T) (len : Q → Result Std.Usize) : Prop :=
  ∀ q, ∃ n, len q = ok n ∧ n.val = (view q).length

/-- Law for `VecDeque::is_empty` (register record
`ks2-ext-alloc-collections-vec-deque-vecdeque-is-empty`).
`is_empty` never panics. It returns `true` exactly when the queue has no element. -/
def VecDequeIsEmptyLaw {Q T : Type} (view : Q → List T) (is_empty : Q → Result Bool) : Prop :=
  ∀ q, ∃ b, is_empty q = ok b ∧ (b = true ↔ view q = [])

/-- Law for `VecDeque::clear` (register record
`ks2-ext-alloc-collections-vec-deque-vecdeque-clear`).
`clear` never panics. The queue it returns is empty. The Lean function returns the new queue.
Idealisation: destruction never panics. `clear` drops the elements, and a destructor may panic
in general. The element type in the verified code is `ZVec`, whose `drop` overwrites the buffer
and calls `munlock`; an `munlock` error is only logged. -/
def VecDequeClearLaw {Q T : Type} (view : Q → List T) (clear : Q → Result Q) : Prop :=
  ∀ q, ∃ q', clear q = ok q' ∧ view q' = []

/-- The length below which `push_back` is assumed to succeed: a 64th of the largest `usize`.
For an element of at most 64 bytes (a `ZVec` has 24), the capacity then stays far below the
limit of `isize::MAX` bytes at which Rust panics with "capacity overflow". -/
def queueBound : Nat := Std.Usize.max / 64

/-- Law for `VecDeque::push_back` (register record
`ks2-ext-alloc-collections-vec-deque-vecdeque-push-back`).
If the queue has fewer than `queueBound` elements, `push_back q x` never panics, and the queue
it returns holds the old elements and then `x`. Nothing is said for longer queues: Rust panics
on capacity overflow there. The bound keeps the laws consistent with `len`, which returns a
`usize`. Idealisation: allocation never fails. -/
def VecDequePushBackLaw {Q T : Type} (view : Q → List T) (push_back : Q → T → Result Q) :
    Prop :=
  ∀ q x, (view q).length < queueBound →
    ∃ q', push_back q x = ok q' ∧ view q' = view q ++ [x]

/-- Law for `VecDeque::split_off` (register record
`ks2-ext-alloc-collections-vec-deque-vecdeque-split-off`).
`split_off q n` splits the queue at index `n`. If `n` is larger than the length, it panics
(`fail`). Otherwise it returns a pair. Following the Aeneas convention for `&mut self`, the first
component is the value Rust returns: the elements from index `n`. The second component is the
queue `q` after the call: the first `n` elements.
Idealisation: allocation never fails. -/
def VecDequeSplitOffLaw {Q T : Type} (view : Q → List T)
    (split_off : Q → Std.Usize → Result (Q × Q)) : Prop :=
  (∀ q n, (view q).length < n.val → split_off q n = fail Error.panic) ∧
  (∀ q n, n.val ≤ (view q).length → ∃ tl hd, split_off q n = ok (tl, hd) ∧
    view tl = (view q).drop n.val ∧ view hd = (view q).take n.val)

/-! ## Standard library -/

/-- The little-endian number of a list of bytes, first byte least significant. -/
def leNat : List Std.U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * leNat bs

/-- Law for `core::mem::size_of` (register record `ks2-ext-core-mem-size-of`).
For the types the code uses, the call never panics and gives the size in bytes: 4 for `u32`,
4 for `i32`, 8 for `i64`. Nothing is said for other types. -/
def CoreMemSizeOfSpec : Prop :=
  (∃ n, core.mem.size_of Std.U32 = ok n ∧ n.val = 4) ∧
  (∃ n, core.mem.size_of Std.I32 = ok n ∧ n.val = 4) ∧
  (∃ n, core.mem.size_of Std.I64 = ok n ∧ n.val = 8)

/-- Law for `from_ne_bytes` on 4 bytes, as a shape: the call never panics and the value has the
little-endian bit pattern of the bytes. -/
def FromNeBytes4Law {α : Type} (bv : α → BitVec 32) (f : Array Std.U8 4#usize → Result α) :
    Prop :=
  ∀ b, ∃ x, f b = ok x ∧ bv x = BitVec.ofNat 32 (leNat b.val)

/-- Law for `from_ne_bytes` on 8 bytes. See `FromNeBytes4Law`. -/
def FromNeBytes8Law {α : Type} (bv : α → BitVec 64) (f : Array Std.U8 8#usize → Result α) :
    Prop :=
  ∀ b, ∃ x, f b = ok x ∧ bv x = BitVec.ofNat 64 (leNat b.val)

/-- Law for `u32::from_ne_bytes` (register record `ks2-ext-core-num-u32-from-ne-bytes`).
Target assumption (little-endian: aarch64 and x86_64 Android): the first byte is the least
significant. The call never panics. -/
def CoreNumU32FromNeBytesSpec : Prop :=
  FromNeBytes4Law (fun x => x.bv) u32FromNeBytes

/-- Law for `i32::from_ne_bytes` (register record `ks2-ext-core-num-i32-from-ne-bytes`).
Target assumption (little-endian: aarch64 and x86_64 Android): the first byte is the least
significant, and the value is the two's complement reading of the bit pattern. The call never
panics. -/
def CoreNumI32FromNeBytesSpec : Prop :=
  FromNeBytes4Law (fun x => x.bv) i32FromNeBytes

/-- Law for `i64::from_ne_bytes` (register record `ks2-ext-core-num-i64-from-ne-bytes`).
Target assumption (little-endian: aarch64 and x86_64 Android): the first byte is the least
significant, and the value is the two's complement reading of the bit pattern. The call never
panics. -/
def CoreNumI64FromNeBytesSpec : Prop :=
  FromNeBytes8Law (fun x => x.bv) i64FromNeBytes

/-- Law for `<[T]>::first` (register record `ks2-ext-core-slice-slice-first`).
For bytes: `first s` never panics. It returns the first byte, or `None` for an empty slice. -/
def CoreSliceFirstSpec : Prop :=
  ∀ s : Slice Std.U8, sliceFirst s = ok s.val.head?

/-- Law for `Vec::truncate` (register record `ks2-ext-alloc-vec-vec-truncate`).
For bytes: `truncate v n` never panics. It keeps the first `n` bytes (all of them if `n` is
larger than the length). It frees memory only. -/
def AllocVecTruncateSpec : Prop :=
  ∀ (v : alloc.vec.Vec Std.U8) (n : Std.Usize),
    ∃ w, vecTruncate alloc.alloc.Global v n = ok w ∧ w.val = v.val.take n.val

/-- Law for the inequality of a slice and a `Vec` (register record
`ks2-ext-shared0slice-insts-corecmppartialeqvec-ne`).
For bytes, with the global allocator: `ne s v` never panics. It returns `true` exactly when the
two byte sequences differ. -/
def Shared0SliceNeSpec : Prop :=
  ∀ (s : Slice Std.U8) (v : alloc.vec.Vec Std.U8),
    ∃ b, sliceVecNe alloc.alloc.Global core.cmp.PartialEqU8 s v
        = ok b ∧ (b = true ↔ s.val ≠ v.val)

/-! ## Crypto and SELinux helpers

Facts that hold for every successful call. Nothing is said about the outcome of a call, about
two calls, or about cryptographic strength: `generate_salt` and the key functions use random
data, and the helpers read the environment. Source: `keystore2/src/crypto/lib.rs`,
`keystore2/src/crypto/zvec.rs`, `keystore2/src/crypto/crypto.cpp`. -/

/-- Law for `ZVec::deref` (register record
`ks2-ext-keystore2-crypto-zvec-zvec-insts-coreopsderefderefsliceu8-deref`).
`deref` never panics: the slice `elems[0..len]` always fits, because `len` never exceeds the
size of the buffer. -/
def ZVecDerefSpec : Prop := TotalLaw zvecDeref

/-- Law for `Deref for keystore2_selinux::Context` (register record
`ks2-ext-keystore2-selinux-context-insts-coreopsderefderefcstr-deref`).
`deref` never panics. Source: `keystore2/selinux/src/lib.rs`, `impl Deref for Context`. -/
def ContextDerefSpec : Prop :=
  TotalLaw contextDeref

/-- Law for `hkdf_expand`, over the observation `deref` of a secret vector as a slice.
If `expand n prk info` returns `Ok z`, then `z` has exactly `n` bytes. Nothing is said when the
call returns `Err` or panics. -/
def HkdfExpandLenLaw {Z : Type} (deref : Z → Result (Slice Std.U8))
    (expand : Std.Usize → Slice Std.U8 → Slice Std.U8 →
      Result (core.result.Result Z keystore2_crypto.error.Error)) : Prop :=
  ∀ n prk info z, expand n prk info = ok (.Ok z) → ∃ s, deref z = ok s ∧ s.length = n.val

/-- Law for `keystore2_crypto::hkdf_expand` (register record
`ks2-ext-keystore2-crypto-hkdf-expand`).
If the call returns `Ok z`, then `z` has the requested length. The view of `z` as a slice is the
`deref` axiom of `ZVec`. Source: `crypto/lib.rs`, `hkdf_expand`, which makes the vector with
`ZVec::new(out_len)`. -/
def KeystoreCryptoHkdfExpandSpec : Prop :=
  HkdfExpandLenLaw zvecDeref
    keystore2_crypto.hkdf_expand

/-- Law for `hkdf_extract`, over the observation `deref` of a secret vector as a slice.
If `extract secret salt` returns `Ok z`, then `z` has 32 bytes, the output size of SHA-256.
Nothing is said when the call returns `Err` or panics. -/
def HkdfExtractLenLaw {Z : Type} (deref : Z → Result (Slice Std.U8))
    (extract : Slice Std.U8 → Slice Std.U8 →
      Result (core.result.Result Z keystore2_crypto.error.Error)) : Prop :=
  ∀ secret salt z, extract secret salt = ok (.Ok z) → ∃ s, deref z = ok s ∧ s.length = 32

/-- Law for `keystore2_crypto::hkdf_extract` (register record
`ks2-ext-keystore2-crypto-hkdf-extract`).
If the call returns `Ok z`, then `z` has 32 bytes. The view of `z` as a slice is the `deref`
axiom of `ZVec`. Source: `crypto/lib.rs`, `hkdf_extract`, which shortens the buffer to the length
BoringSSL reports, and `crypto/crypto.cpp`, which fixes the digest to SHA-256. That the report
is 32 is a fact about BoringSSL, not about this repository. -/
def KeystoreCryptoHkdfExtractSpec : Prop :=
  HkdfExtractLenLaw zvecDeref
    keystore2_crypto.hkdf_extract

/-- Law for the result of a call that returns a salt. If the call returns `Ok s`, then `s`
has 16 bytes (`SALT_LENGTH`). Nothing is said when it returns `Err` or panics. -/
def SaltLenLaw {E : Type} (gen : Result (core.result.Result (alloc.vec.Vec Std.U8) E)) : Prop :=
  ∀ s, gen = ok (.Ok s) → s.val.length = 16

/-- Law for `keystore2_crypto::generate_salt` (register record
`ks2-ext-keystore2-crypto-generate-salt`).
If the call returns `Ok s`, then `s` has 16 bytes. Nothing is said about the bytes: they are
random. Source: `crypto/lib.rs`, `generate_salt` and `generate_random_data`. -/
def KeystoreCryptoGenerateSaltSpec : Prop := SaltLenLaw keystore2_crypto.generate_salt

/-- Law for `keystore2_crypto::hmac_sha256` (register record
`ks2-ext-keystore2-crypto-hmac-sha256`).
If the call returns `Ok v`, then `v` has 32 bytes (`HMAC_SHA256_LEN`). Nothing is said about
the bytes or about the other outcomes. Source: `crypto/lib.rs`, `hmac_sha256`, which returns a
vector made as `vec![0; HMAC_SHA256_LEN]`. -/
def KeystoreCryptoHmacSha256Spec : Prop :=
  ∀ key msg v, keystore2_crypto.hmac_sha256 key msg = ok (.Ok v) → v.val.length = 32

end Keystore2Verify.Externals
