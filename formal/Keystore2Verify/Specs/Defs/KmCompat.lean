import Keystore2Verify.Specs.Defs.Externals

/-!
# Definitions for the statements about `km_compat.rs`

The bytes that `unwrap_keyblob` looks at, and two assumptions about external functions: the
prefix test `starts_with` and the comparison of a slice with a vector. Nothing here is an
axiom.
-/

namespace Keystore2Verify.KmCompat
open Aeneas Aeneas.Std Result keystore2
open keystore2.core.slice.Slice renaming starts_with → sliceStartsWith
open keystore2.Shared0Slice.Insts.CoreCmpPartialEqVec renaming eq → sliceVecEq

/-- The bytes of `keyblob` after the wrapper prefix `KEYBLOB_PREFIX`. -/
def unwrapRest (keyblob : Slice Std.U8) : List Std.U8 :=
  keyblob.val.drop km_compat.KEYBLOB_PREFIX.length

/-- The inner key blob of a wrapped blob: the bytes after the prefix, without the last `n`
bytes. Here `n` is the length of an HMAC-SHA256 tag. -/
def unwrapInner (keyblob : Slice Std.U8) (n : Nat) : List Std.U8 :=
  (unwrapRest keyblob).take ((unwrapRest keyblob).length - n)

/-- The tag of a wrapped blob: the last `n` bytes after the prefix. -/
def unwrapTag (keyblob : Slice Std.U8) (n : Nat) : List Std.U8 :=
  (unwrapRest keyblob).drop ((unwrapRest keyblob).length - n)

/-- Assumption about an external function: `<[T]>::starts_with` (register record
`ks2-ext-core-slice-slice-starts-with`). For bytes: `f s p` never panics, and it returns `true`
exactly when the bytes `p` are a prefix of the bytes `s`. -/
def CoreSliceStartsWithAssumption (f : Slice Std.U8 → Slice Std.U8 → Result Bool) : Prop :=
  ∀ s p : Slice Std.U8, ∃ b, f s p = ok b ∧ (b = true ↔ p.val <+: s.val)

/-- The assumption `CoreSliceStartsWithAssumption` at the extracted `starts_with` for bytes. -/
def CoreSliceStartsWithSpec : Prop :=
  CoreSliceStartsWithAssumption (sliceStartsWith core.cmp.PartialEqU8)

/-- Assumption about an external function: the equality `&[u8] == Vec<u8>` (register record
`ks2-ext-shared0slice-insts-corecmppartialeqvec-eq`). `f s v` never panics, and it returns `true`
exactly when the two byte sequences are equal. -/
def Shared0SliceEqAssumption (f : Slice Std.U8 → alloc.vec.Vec Std.U8 → Result Bool) : Prop :=
  ∀ (s : Slice Std.U8) (v : alloc.vec.Vec Std.U8),
    ∃ b, f s v = ok b ∧ (b = true ↔ s.val = v.val)

/-- The assumption `Shared0SliceEqAssumption` at the extracted equality, with the global
allocator. -/
def Shared0SliceEqSpec : Prop :=
  Shared0SliceEqAssumption (sliceVecEq alloc.alloc.Global core.cmp.PartialEqU8)

end Keystore2Verify.KmCompat
