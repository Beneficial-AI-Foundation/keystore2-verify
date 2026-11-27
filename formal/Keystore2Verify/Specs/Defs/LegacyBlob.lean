import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `legacy_blob.rs`

Pure helper definitions, and new assumptions about external functions that the statements of
`legacy_blob.rs` need. Nothing here is an axiom and nothing is proved.

The model of formatting is erased (see `Externals.lean`): the text built by `format!` is not
observable, so the statements about file names say that a final path component is pushed, not
which text it holds. The file system is not modelled either: a call that reads or changes it is an
inline hypothesis of the theorem.
-/

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open keystore2_crypto.zvec.ZVec.Insts renaming CoreCmpPartialEqZVec.eq → zvecEqFn
open keystore2.alloc.vec.Vec.Insts.CoreCmpOrd renaming cmp → vecCmpFn
open keystore2.std.path.Path renaming read_dir → pathReadDirFn
open keystore2.std.path.Path.Insts renaming CoreConvertAsRefPath → pathAsRefPath
open keystore2.std.path.PathBuf.Insts renaming CoreConvertAsRefPath → pathBufAsRefPath
open Aeneas.Std.core.iter.traits.iterator renaming Iterator → IteratorTrait
open Aeneas.Std.core.ops.function renaming FnMut → FnMutTrait
open key_parameter.KeyParameter.Insts renaming CoreCmpOrd → kpOrdInst
open keystore2.alloc.string.String.Insts renaming CoreConvertAsRefPath → stringAsRefPath
open keystore2.alloc.string.String.Insts.CoreOpsDerefDerefStr renaming deref → stringDeref
open keystore2.alloc.string.String renaming from_utf8 → stringFromUtf8
open keystore2.alloc.string.ToString.Blanket renaming to_string → toStringBlanket
open keystore2.alloc.vec.Vec.Insts.CoreDefaultDefault renaming default → vecDefault
open Aeneas.Std.alloc.vec.into_iter renaming IntoIter → VecIntoIter
open keystore2.core.io.error renaming Error → ioErrorTy
open keystore2.core.io.error.Error renaming kind → ioErrorKindFn
open keystore2.core.io.error renaming ErrorKind → ioErrorKindTy
open keystore2.core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind renaming eq → ioKindEqFn
open keystore2.core.io.error.ErrorKind renaming Interrupted → kindInterrupted
open keystore2.core.io.error.ErrorKind renaming NotFound → kindNotFound
open keystore2.core.iter.adapters.chain renaming Chain → ChainAdapter
open keystore2.core.iter.adapters.chain.Chain.Insts renaming
  CoreIterTraitsIteratorIterator → chainIteratorInst
open keystore2.core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator renaming
  next → chainNext
open keystore2.core.iter.adapters.flatten renaming Flatten → FlattenAdapter
open keystore2.core.iter.adapters.flatten.Flatten.Insts renaming
  CoreIterTraitsIteratorIterator → flattenIteratorInst
open Aeneas.Std.core.iter.adapters.map renaming Map → MapAdapter
open keystore2.core.iter.adapters.map.Map.Insts renaming
  CoreIterTraitsIteratorIterator → mapIteratorInst
open Aeneas.Std.core.iter.traits.collect.IntoIterator renaming Blanket → intoIteratorBlanket
open keystore2.core.iter.traits.iterator.Iterator.chain renaming default → chainDefault
open keystore2.core.iter.traits.iterator.Iterator.flatten renaming default → flattenDefault
open keystore2.core.iter.traits.iterator.Iterator.map renaming default → mapDefault
open Aeneas.Std.core.iter.traits.iterator renaming IteratorVecIntoIter → vecIntoIterInst
open Aeneas.Std.core.ops.function renaming Fn → FnTrait
open Aeneas.Std.core.ops.function renaming FnOnce → FnOnceTrait
open keystore2.core.option.IntoIter.Insts renaming CoreIterTraitsIteratorIterator → optionIterInst
open keystore2.core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter renaming
  into_iter → optionIntoIter
open keystore2.core.option.Option renaming and_then → optionAndThen
open keystore2.core.str.Str renaming bytes → strBytes
open keystore2.core.str.iter renaming Bytes → BytesIter
open keystore2.core.str.iter.Bytes.Insts.CoreIterTraitsIteratorIteratorU8 renaming next → bytesNext
open keystore2.legacy_blob.LegacyBlobLoader.read_characteristics_file renaming closure → hwClosure
open keystore2.legacy_blob.LegacyBlobLoader.read_characteristics_file renaming closure_1 → swClosure
open keystore2.std.ffi.os_str.OsStr renaming to_str → osStrToStr
open keystore2.std.ffi.os_str.OsString.Insts.CoreOpsDerefDerefOsStr renaming deref → osStringDeref
open keystore2.std.fs.DirEntry renaming file_name → dirEntryFileName
open keystore2.std.path.PathBuf.Insts.CoreCloneClone renaming clone → pathBufClone
open keystore2.std.path.PathBuf.Insts.CoreOpsDerefDerefPath renaming deref → pathBufDerefFn
open keystore2.std.path.PathBuf renaming push → pathBufPush
open alloc.string.String.Insts renaming CoreFmtDisplay → StringDisplay
open legacy_blob.Error.Insts renaming CoreErrorError → legacyErrorInst
open alloc.string.FromUtf8Error.Insts renaming CoreErrorError → utf8ErrorInst
open core.io.error.Error.Insts renaming CoreErrorError → ioErrorInst
open error.Error.Insts renaming CoreErrorError → ksErrorInst
open keystore2_crypto.zvec.Error.Insts renaming CoreErrorError → zvecErrorInst

/-- The security level of a key parameter. -/
abbrev SecLevel : Type := SecurityLevel.SecurityLevel

/-- An `io::Error`. -/
abbrev IoError : Type := ioErrorTy

/-- An `io::ErrorKind`. -/
abbrev IoErrorKind : Type := ioErrorKindTy

/-- The kind of an `io::Error` (the external function `Error::kind`). -/
noncomputable abbrev ioErrorKind : IoError → Result IoErrorKind := ioErrorKindFn

/-- The comparison of two kinds (the external function `ErrorKind::eq`). -/
noncomputable abbrev ioKindEq : IoErrorKind → IoErrorKind → Result Bool :=
  ioKindEqFn

/-- The kind `NotFound`. -/
def ioNotFound : IoErrorKind := kindNotFound

/-- The kind `Interrupted`. -/
def ioInterrupted : IoErrorKind := kindInterrupted

/-- The view of a path buffer as a path (the external function `PathBuf::deref`). -/
noncomputable abbrev pathBufDeref : std.path.PathBuf → Result std.path.Path :=
  pathBufDerefFn

/-- The view of a `String` as a `&str` (the external function `String::deref`). -/
noncomputable abbrev stringAsStr : String → Result Str := stringDeref

/-- The clone of a path buffer (the external function `PathBuf::clone`). -/
noncomputable abbrev pathBufCloneFn : std.path.PathBuf → Result std.path.PathBuf := pathBufClone

/-- Pushing a `String` component onto a path buffer (the external function `PathBuf::push`). -/
noncomputable abbrev pathPushString : std.path.PathBuf → String → Result std.path.PathBuf :=
  pathBufPush stringAsRefPath

/-- Assumption about an external function (register record
`ks2-ext-core-io-error-errorkind-insts-corecmppartialeqerrorkind-eq`). `ErrorKind::eq` never panics
and returns `true` exactly when the two kinds are the same. -/
def IoKindEqSpec : Prop :=
  ∀ a b : IoErrorKind, ∃ r, ioKindEq a b = ok r ∧ (r = true ↔ a = b)

/-- Removing a file (the external function `fs::remove_file`, as the closure of the retry loop
calls it). -/
noncomputable abbrev removeFileCall : std.path.Path → Result (core.result.Result Unit IoError) :=
  std.fs.remove_file (Shared0T.Insts.CoreConvertAsRef pathAsRefPath)

/-- Removing a directory (the external function `fs::remove_dir`, as the closure of the retry loop
calls it). -/
noncomputable abbrev removeDirCall : std.path.Path → Result (core.result.Result Unit IoError) :=
  std.fs.remove_dir (Shared0T.Insts.CoreConvertAsRef pathAsRefPath)

/-- Reading a directory by `fs::read_dir`, as the closure of `list_user` calls it. -/
noncomputable abbrev readDirCall :
    std.path.Path → Result (core.result.Result std.fs.ReadDir IoError) :=
  std.fs.read_dir (Shared0T.Insts.CoreConvertAsRef pathAsRefPath)

/-- Reading a directory by `Path::read_dir`, as the closure of `is_empty_user` calls it. -/
noncomputable abbrev pathReadDirCall :
    std.path.Path → Result (core.result.Result std.fs.ReadDir IoError) :=
  pathReadDirFn

/-- Renaming a file (the external function `fs::rename`, as the closure of
`move_keystore_file_if_exists` calls it). -/
noncomputable abbrev renameCall :
    std.path.PathBuf → std.path.PathBuf → Result (core.result.Result Unit IoError) :=
  std.fs.rename (Shared0T.Insts.CoreConvertAsRef pathBufAsRefPath)
    (Shared0T.Insts.CoreConvertAsRef pathBufAsRefPath)

/-- A call that the retry loop does not repeat: it returns `Ok`, or an error whose kind is not
`Interrupted`. A statement that takes this as a hypothesis covers a run whose first call is not
interrupted. -/
def CallReturns {T : Type} (c : Result (core.result.Result T IoError)) : Prop :=
  (∃ v, c = ok (.Ok v)) ∨
    (∃ e k, c = ok (.Err e) ∧ ioErrorKind e = ok k ∧ k ≠ ioInterrupted)

/-- The instance of a closure that `with_retry_interrupted` calls. -/
abbrev RetryFn (F T : Type) : Type :=
  FnTrait F Unit (core.result.Result T IoError)

/-- The byte iterator of a string. -/
abbrev StrBytesIter : Type := BytesIter

/-- A successful result of reading a directory entry. -/
def okEntry (d : std.fs.DirEntry) : core.result.Result std.fs.DirEntry IoError := .Ok d

/-- The flag bit `i` of a blob: whether bit `i` of its flag byte is set. -/
def flagSet (b : legacy_blob.Blob) (i : Nat) : Bool := Nat.testBit b.flags.val i

/-! ## Text helpers -/

/-- The bytes of the UTF-8 encoding of a string. -/
def utf8Bytes (s : String) : List Std.U8 :=
  List.map (fun b => ⟨b.toBitVec⟩) s.toUTF8.toList

/-- A byte list is valid UTF-8 when some string has it as its encoding. -/
def ValidUtf8 (bs : List Std.U8) : Prop := ∃ s, utf8Bytes s = bs

/-- The state machine of `LegacyBlobLoader::decode_alias`, on the numeric values of the bytes.
`decodeNat multi bytes acc` reads `bytes` with the pending first half `multi` of a two-byte
sequence and the decoded bytes `acc`. It returns `none` where the Rust code returns
`Error::BadEncoding`, and the decoded bytes at the end of the input. The arms are those of the
Rust `match`: `'0'..='o'` with a pending half completes it (`m | (c - '0')`); `'+'..='.'` with no
pending half starts one (`(c - '+') << 6`); `'0'..='~'` with no pending half is a literal byte;
every other pair is an error. -/
def decodeNat : Option Nat → List Nat → List Nat → Option (List Nat)
  | some m, c :: cs, acc =>
      if 48 ≤ c ∧ c ≤ 111 then decodeNat none cs (acc ++ [m ||| (c - 48)]) else none
  | none, c :: cs, acc =>
      if 43 ≤ c ∧ c ≤ 46 then decodeNat (some ((c - 43) <<< 6)) cs acc
      else if 48 ≤ c ∧ c ≤ 126 then decodeNat none cs (acc ++ [c]) else none
  | some _, [], _ => none
  | none, [], acc => some acc

/-- The path that `PathBuf::push` gives, on the bytes of the path: pushing an absolute component
replaces the path; otherwise a `/` is added when the path is not empty and does not end in `/`. -/
def pathPush (base s : List Std.U8) : List Std.U8 :=
  if s.head? = some 47#u8 then s
  else if base = [] ∨ base.getLast? = some 47#u8 then base ++ s
  else base ++ [47#u8] ++ s

/-! ## `context` calls

The assumptions at the `context` calls of this file. Each is `ResultContextLaw` at one error
type, so the root cause of the new error is the class of the old one. `ErrRoot` has no
constructor for the error types `legacy_blob::Error`, `FromUtf8Error`, `io::Error` and
`keystore2_crypto::zvec::Error`, so their class is `other`. -/

section
open core.result.Result.Insts.AnyhowContext
open anyhow.context.ext.StdError

/-- The `context` assumption at a call `result.context(..)` where `result` holds an error of a
standard error type `E` and a value of type `T`. -/
abbrev BlanketCtxLaw {E : Type} (inst : core.error.Error E) (rootE : E → ErrRoot)
    (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw rootE root (context (T := T) (Blanket inst) StringDisplay)

/-- The `context` assumption for a `legacy_blob::Error` (class `other`). -/
abbrev LegacyErrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  BlanketCtxLaw legacyErrorInst (fun _ => ErrRoot.other) root T

/-- The `context` assumption for a `FromUtf8Error` (class `other`). -/
abbrev Utf8ErrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  BlanketCtxLaw utf8ErrorInst (fun _ => ErrRoot.other) root T

/-- The `context` assumption for an `io::Error` (class `other`). -/
abbrev IoErrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  BlanketCtxLaw ioErrorInst (fun _ => ErrRoot.other) root T

/-- The `context` assumption for a `keystore2::error::Error` (class `ks`). -/
abbrev KsErrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  BlanketCtxLaw ksErrorInst (fun x => ErrRoot.ks x) root T

/-- The `context` assumption for a `keystore2_crypto::zvec::Error` (class `other`). -/
abbrev ZVecErrCtxLaw (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  BlanketCtxLaw zvecErrorInst (fun _ => ErrRoot.other) root T

end

/-- The assumptions that every `format!` and `ks_err!` in this file needs: the two calls that
build the message do not panic. Assumptions about external functions, both stated in
`Externals.lean`. -/
def MessageSpecs : Prop := AllocFmtFormatSpec ∧ CoreFmtArgumentsFromStrNonconstSpec

/-- The assumptions that a log statement in this file needs: the five calls of the `info!` and
`warn!` expansions do not panic. Assumptions about external functions, all stated in
`Externals.lean`. -/
def LogSpecs : Prop :=
  LogMaxLevelSpec ∧ LogLevelPartialCmpSpec ∧ LogLocSpec ∧ LogPrivateApiLogSpec

/-! ## Iteration over the bytes of a string -/

/-- Assumption about an external function (register record `ks2-ext-core-str-str-bytes`).
`s.bytes()` never panics. Seen through `view`, the iterator yields the bytes of `s` in order. -/
def StrBytesSpec (view : BytesIter → List Std.U8) : Prop :=
  ∀ s : Str, ∃ it, strBytes s = ok it ∧ view it = s.val

/-- The shape of an assumption for `Iterator::next`. Seen through `view`, `next` never panics. It
returns the first element (or `none` when no element is left) and an iterator for the rest. -/
def NextAssumption {I T : Type} (view : I → List T)
    (next : I → Result (Option T × I)) : Prop :=
  ∀ it, ∃ o it', next it = ok (o, it') ∧
    (view it = [] → o = none ∧ view it' = []) ∧
    (∀ x xs, view it = x :: xs → o = some x ∧ view it' = xs)

/-- Assumption about an external function (register record
`ks2-ext-core-str-iter-bytes-insts-coreitertraitsiteratoriteratoru8-next`).
It is `NextAssumption` for the byte iterator of a string. -/
def BytesNextSpec (view : BytesIter → List Std.U8) : Prop :=
  NextAssumption view bytesNext

/-- Assumption about an external function (register record `ks2-ext-alloc-string-string-from-utf8`).
`String::from_utf8 v` never panics. It returns `Ok s` when `v` is valid UTF-8, and then `s` has
the bytes of `v`; otherwise it returns `Err`. -/
def StringFromUtf8Spec : Prop :=
  ∀ v : alloc.vec.Vec Std.U8, ∃ r, stringFromUtf8 v = ok r ∧
    (∀ s, r = .Ok s → utf8Bytes s = v.val) ∧ (∀ e, r = .Err e → ¬ ValidUtf8 v.val)

/-! ## Paths

`view` is the observation of a `PathBuf`: the bytes of the path. -/

/-- Assumption about an external function (register record
`ks2-ext-std-path-pathbuf-insts-corecloneclone-clone`).
`clone` never panics and returns a path with the same bytes. Idealisation: allocation never
fails. -/
def PathBufCloneSpec (view : std.path.PathBuf → List Std.U8) : Prop :=
  ∀ p, ∃ q, pathBufClone p = ok q ∧ view q = view p

/-- The shape of the assumption for `PathBuf::push` at a type `A` of path components, with `bytes`
the bytes of a component: `push p a` never panics and returns the path `pathPush (view p) (bytes
a)`. Idealisation: allocation never fails. -/
def PathBufPushAssumption {A : Type} (view : std.path.PathBuf → List Std.U8)
    (bytes : A → List Std.U8) (inst : core.convert.AsRef A std.path.Path) : Prop :=
  ∀ p a, ∃ q, pathBufPush inst p a = ok q ∧ view q = pathPush (view p) (bytes a)

/-- Assumption about an external function (register record `ks2-ext-std-path-pathbuf-push`), for a
component of type `String`. It is `PathBufPushAssumption` with the bytes of the string. -/
def PathBufPushStringSpec (view : std.path.PathBuf → List Std.U8) : Prop :=
  PathBufPushAssumption view utf8Bytes stringAsRefPath

/-- Assumption about an external function (register record `ks2-ext-std-path-pathbuf-push`), for
a component of type `&str`. It is `PathBufPushAssumption` with the bytes of the string. -/
def PathBufPushStrSpec (view : std.path.PathBuf → List Std.U8) : Prop :=
  PathBufPushAssumption view (fun s : Str => s.val)
    (Shared0T.Insts.CoreConvertAsRef Str.Insts.CoreConvertAsRefPath)

/-! ## Other standard-library calls -/

/-- Assumption about an external function (register record
`ks2-ext-alloc-vec-vec-insts-coredefaultdefault-default`), for `Vec<String>`.
`default` never panics and returns the empty vector. -/
def VecStringDefaultSpec : Prop :=
  ∃ v, vecDefault String = ok v ∧ v.val = []

/-- Assumption about an external function (register record
`ks2-ext-alloc-string-tostring-blanket-to-string`), for `&str`.
For a `&str` whose bytes are valid UTF-8, `to_string` never panics and returns a string with the
bytes of the `&str`. Nothing is said for other byte lists: the Rust type `&str` is always valid
UTF-8, but the translated type is a slice of bytes. Idealisation: allocation never fails, and
formatting never panics. -/
def StrToStringSpec : Prop :=
  ∀ f : Str, ValidUtf8 f.val → ∃ s, toStringBlanket Str.Insts.CoreFmtDisplay f = ok s ∧
    utf8Bytes s = f.val

/-- Assumption about an external function (register record `ks2-ext-std-ffi-os-str-osstr-to-str`).
If `OsStr::to_str` returns `Some f`, the bytes of `f` are valid UTF-8. Source: the result is a
`&str`. -/
def OsStrToStrSpec : Prop :=
  ∀ os f, osStrToStr os = ok (some f) → ValidUtf8 f.val

/-- Assumption about an external function (register record `ks2-ext-core-option-option-and-then`).
`and_then` keeps `none`, and applies the closure to the value of a `some`. The statement
holds for a closure whose call has no side effect other than the call itself. -/
def OptionAndThenSpec {T U F : Type} (inst : FnOnceTrait F T (Option U)) : Prop :=
  ∀ f : F, optionAndThen inst none f = ok none ∧
    ∀ x, optionAndThen inst (some x) f = inst.call_once f x

/-! ## Iterators over directory entries

The iterator `next` is an external function that reads the file system. A theorem takes the
sequence of its results as one hypothesis, `NextRun`: the iterator yields the listed items and
then `none`. -/

/-- The iterator `it` yields exactly the items `es`, one `next` call each, and then `none`. -/
def NextRun {I T : Type} (next : I → Result (Option T × I)) : I → List T → Prop
  | it, [] => ∃ it', next it = ok (none, it')
  | it, e :: es => ∃ it', next it = ok (some e, it') ∧ NextRun next it' es

/-- The iterator `it` yields the items `es` in order, one `next` call each, and the iterator that
remains after them is `it'`. The empty list needs no call. The result of any later call is not
constrained. -/
def NextPrefix {I T : Type} (next : I → Result (Option T × I)) : I → List T → I → Prop
  | it, [], it' => it' = it
  | it, e :: es, it' => ∃ it1, next it = ok (some e, it1) ∧ NextPrefix next it1 es it'

/-- The file name of the directory entry `d` is `o`: the three calls that read it return. -/
def FileNameIs (d : std.fs.DirEntry) (o : Option Str) : Prop :=
  ∃ os os', dirEntryFileName d = ok os ∧
    osStringDeref os = ok os' ∧
    osStrToStr os' = ok o

/-! ## Variants -/

/-- The position of a variant of `legacy_blob::Error`, in declaration order. -/
def errorIndex : legacy_blob.Error → Nat
  | .BadLen => 0
  | .BadEncoding => 1
  | .LockedComponent => 2
  | .AndroidUserMismatch => 3

/-- The position of a variant of `BlobValue`, in declaration order. -/
def blobValueIndex : legacy_blob.BlobValue → Nat
  | .Generic _ => 0
  | .Characteristics _ => 1
  | .EncryptedCharacteristics _ _ _ => 2
  | .CharacteristicsCache _ => 3
  | .PwEncrypted _ _ _ _ _ => 4
  | .Encrypted _ _ _ => 5
  | .EncryptedGeneric _ _ _ => 6
  | .Decrypted _ => 7

/-- The position of a variant of `LegacyKeyCharacteristics`, in declaration order. -/
def characteristicsIndex : legacy_blob.LegacyKeyCharacteristics → Nat
  | .Cache _ => 0
  | .File _ => 1

/-- A blob value that holds key characteristics: the value of a file that
`read_characteristics_file` accepts. -/
def IsCharacteristics (v : legacy_blob.BlobValue) : Prop :=
  (∃ d, v = .Characteristics d) ∨ (∃ d, v = .CharacteristicsCache d)

/-! ## Comparisons -/

/-- The lexicographic order on lists, given the order `c` of the elements: the first difference
decides, and a proper prefix is smaller. -/
def lexOrd {T : Type} (c : T → T → Ordering) : List T → List T → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | x :: xs, y :: ys => match c x y with
    | Ordering.eq => lexOrd c xs ys
    | o => o

/-- The vector of a `LegacyKeyCharacteristics`, as a list. -/
def lkcList : legacy_blob.LegacyKeyCharacteristics → List key_parameter.KeyParameter
  | .Cache v => v.val
  | .File v => v.val

/-- The order of two `LegacyKeyCharacteristics` that the derived `Ord` gives, from the order `c` of
the key parameters: `Cache` is smaller than `File`; two values of one variant compare as their
vectors. -/
def lkcOrder (c : key_parameter.KeyParameter → key_parameter.KeyParameter → Ordering)
    (a b : legacy_blob.LegacyKeyCharacteristics) : Ordering :=
  if characteristicsIndex a < characteristicsIndex b then Ordering.lt
  else if characteristicsIndex b < characteristicsIndex a then Ordering.gt
  else lexOrd c (lkcList a) (lkcList b)

/-- Assumption about an external function (register record
`ks2-ext-keystore2-crypto-zvec-zvec-insts-corecmppartialeqzvec-eq`).
`ZVec::eq` never panics. `view` gives what the derived comparison reads: the whole buffer `elems`
and the length `len`. The buffer can hold bytes after `len` (`try_from` fills the vector to its
capacity, `reduce_len` keeps the allocation), so two vectors with the same secret bytes can compare
unequal. `view` is not the slice that `deref` gives. The result is `true` exactly when the views
are equal. -/
def ZVecEqSpec {α : Type} (view : keystore2_crypto.zvec.ZVec → α) : Prop :=
  ∀ a b, ∃ r, zvecEqFn a b = ok r ∧ (r = true ↔ view a = view b)

/-- Assumption about an external function (register record
`ks2-ext-alloc-vec-vec-insts-corecmpord-cmp`), for the vector of key parameters with the global
allocator. If the order of the elements is `c`, that is, comparing two elements returns `c x y`,
then `Vec::cmp` never panics and returns the lexicographic order. -/
def VecCmpSpec (c : key_parameter.KeyParameter → key_parameter.KeyParameter → Ordering) :
    Prop :=
  (∀ x y, kpOrdInst.cmp x y = ok (c x y)) →
    ∀ a b, vecCmpFn alloc.alloc.Global kpOrdInst a b = ok (lexOrd c a.val b.val)

/-! ## The iterator chain of `read_characteristics_file`

`read_characteristics_file` builds its result with
`hw_list.into_iter().flatten().chain(sw_list).collect()`. The adapters are external types, observed
here through list views: `viewHw` and `viewSw` for the two `map` adapters, `viewOpt` for the
`Option` iterator, `viewFlat` for the `flatten` adapter and `viewChain` for the `chain` adapter. The
views are parameters; the assumptions below say how each external function acts on them. The `Vec`
iterator `into_iter` is a Rust-translated item and is viewed as its list. -/

section CharPipeline

open legacy_blob.LegacyBlobLoader.read_characteristics_file
open legacy_blob.LegacyBlobLoader.read_characteristics_file.closure.Insts renaming
  CoreOpsFunctionFnMutTupleKeyParameterValueKeyParameter → hwFnMutInst
open legacy_blob.LegacyBlobLoader.read_characteristics_file.closure_1.Insts renaming
  CoreOpsFunctionFnMutTupleKeyParameterValueKeyParameter → swFnMutInst

/-- The iterator of a vector of key parameter values. -/
abbrev KpvIntoIter := VecIntoIter key_parameter.KeyParameterValue

/-- The `map` adapter with the closure that tags a value with the hardware security level. -/
abbrev HwMap := MapAdapter KpvIntoIter
  hwClosure

/-- The `map` adapter with the closure that tags a value with `SecurityLevel::KEYSTORE`. -/
abbrev SwMap := MapAdapter KpvIntoIter
  swClosure

/-- The iterator over the `Option` of the hardware list. -/
abbrev HwOpt := core.option.IntoIter HwMap

/-- The `flatten` adapter over the hardware list. -/
abbrev HwFlat := FlattenAdapter HwOpt HwMap key_parameter.KeyParameter HwMap

/-- The `chain` adapter of the two lists. -/
abbrev ParamChain := ChainAdapter HwFlat SwMap

/-- The iterator instance of the `Vec` iterator. -/
noncomputable abbrev kpvIterInst :=
  vecIntoIterInst key_parameter.KeyParameterValue

/-- The `FnMut` instance of the closure for the hardware security level. -/
noncomputable abbrev hwFnMut := hwFnMutInst

/-- The `FnMut` instance of the closure for `SecurityLevel::KEYSTORE`. -/
noncomputable abbrev swFnMut := swFnMutInst

/-- The iterator instance of `HwMap`. -/
noncomputable abbrev hwMapIter :=
  mapIteratorInst kpvIterInst hwFnMut

/-- The iterator instance of `SwMap`. -/
noncomputable abbrev swMapIter :=
  mapIteratorInst kpvIterInst swFnMut

/-- The iterator instance of `HwOpt`. -/
noncomputable abbrev hwOptIter := optionIterInst HwMap

/-- The `IntoIterator` instance of `HwMap` (an iterator is its own `IntoIterator`). -/
noncomputable abbrev hwMapInto := intoIteratorBlanket hwMapIter

/-- The `IntoIterator` instance of `SwMap`. -/
noncomputable abbrev swMapInto := intoIteratorBlanket swMapIter

/-- The iterator instance of `HwFlat`. -/
noncomputable abbrev hwFlatIter :=
  flattenIteratorInst hwOptIter hwMapInto
    hwMapIter

/-- A key parameter with a value and a security level. -/
def mkKeyParameter (v : key_parameter.KeyParameterValue)
    (sl : SecLevel) : key_parameter.KeyParameter :=
  { value := v, security_level := sl }

/-- The shape of the assumption for `Iterator::map` (register record
`ks2-ext-core-iter-traits-iterator-iterator-map-default`). If each call of the closure `f` returns
`g a` and leaves the closure unchanged, `map` never panics and the adapter yields `g` of each
item, in order. -/
def MapAssumption {I F A B : Type} (iterInst : IteratorTrait I A) (fnInst : FnMutTrait F A B)
    (viewIn : I → List A) (viewOut : MapAdapter I F → List B) : Prop :=
  ∀ (it : I) (f : F) (g : A → B), (∀ a, fnInst.call_mut f a = ok (g a, f)) →
    ∃ m, mapDefault iterInst fnInst it f = ok m ∧ viewOut m = (viewIn it).map g

/-- Assumption about an external function (register record
`ks2-ext-core-iter-traits-iterator-iterator-map-default`), for the closure that tags a value with
a security level. It is `MapAssumption` for the closure of the hardware list. -/
def MapHwSpec (viewHw : HwMap → List key_parameter.KeyParameter) : Prop :=
  MapAssumption kpvIterInst hwFnMut (fun it : KpvIntoIter => it.val) viewHw

/-- Assumption about an external function (register record
`ks2-ext-core-iter-traits-iterator-iterator-map-default`), for the closure that tags a value with
`SecurityLevel::KEYSTORE`. It is `MapAssumption` for the closure of the software list. -/
def MapSwSpec (viewSw : SwMap → List key_parameter.KeyParameter) : Prop :=
  MapAssumption kpvIterInst swFnMut (fun it : KpvIntoIter => it.val) viewSw

/-- Assumption about an external function (register record
`ks2-ext-core-option-option-insts-coreitertraitscollectintoiteratortintoiter-into-iter`).
`Option::into_iter` never panics. Seen through `viewOpt`, the iterator yields the value of a
`some`, and nothing for `none`. -/
def OptionIntoIterSpec (viewOpt : HwOpt → List HwMap) : Prop :=
  ∀ o : Option HwMap, ∃ it,
    optionIntoIter o = ok it ∧
    viewOpt it = o.toList

/-- Assumption about an external function (register record
`ks2-ext-core-iter-traits-iterator-iterator-flatten-default`).
`flatten` never panics. Seen through the views, the adapter yields the items of each inner
iterator in turn. -/
def FlattenSpec (viewOpt : HwOpt → List HwMap)
    (viewHw : HwMap → List key_parameter.KeyParameter)
    (viewFlat : HwFlat → List key_parameter.KeyParameter) : Prop :=
  ∀ it, ∃ f,
    flattenDefault hwOptIter hwMapInto it = ok f ∧
    viewFlat f = (viewOpt it).flatMap viewHw

/-- Assumption about an external function (register record
`ks2-ext-core-iter-traits-iterator-iterator-chain-default`).
`chain` never panics. Seen through the views, the adapter yields the items of the first iterator
and then those of the second. -/
def ChainSpec (viewFlat : HwFlat → List key_parameter.KeyParameter)
    (viewSw : SwMap → List key_parameter.KeyParameter)
    (viewChain : ParamChain → List key_parameter.KeyParameter) : Prop :=
  ∀ f m, ∃ c,
    chainDefault hwFlatIter swMapInto f m = ok c ∧
    viewChain c = viewFlat f ++ viewSw m

/-- Assumption about an external function (register record
`ks2-ext-core-iter-adapters-chain-chain-insts-coreitertraitsiteratoriterator-next`).
It is `NextAssumption` for the `chain` adapter. -/
def ChainNextSpec (viewChain : ParamChain → List key_parameter.KeyParameter) : Prop :=
  NextAssumption viewChain
    (chainNext hwFlatIter
      swMapIter)

end CharPipeline

end Keystore2Verify.LegacyBlob
