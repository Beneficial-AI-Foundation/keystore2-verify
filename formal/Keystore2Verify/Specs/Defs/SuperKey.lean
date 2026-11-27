import Keystore2Verify.Specs.Defs.Globals

/-! # Definitions for the statements about `super_key.rs`

The hash maps of the blob metadata and of the super key manager, and the `Arc` and `Option` helpers
that the translated functions call. The general assumptions are in `Specs.Defs.Globals`. Nothing
here is an axiom. -/

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals
open alloc.alloc.Global
open alloc.sync.Arc
open alloc.sync.Arc.Insts
open core.option
open std.collections.hash.map
open std.collections.hash.map.HashMapKVSGlobal.Insts
open std.hash.random.RandomState
open utils.AndroidUserId

/-! ## Blob metadata -/

/-- The entries of the map of a `BlobMetaData`, by tag. -/
abbrev MetaEntries : Type := Entries Std.I64 database.BlobMetaEntry

open std.hash.random.RandomState.Insts renaming CoreHashBuildHasherDefaultHasher → rsHasher
open core.borrow.Borrow renaming Blanket → borrowSelf

/-- `HashMap::get` on the map of a `BlobMetaData`. -/
abbrev MetaGetSpec (ents : MetaEntries) : Prop :=
  HashMapGetAssumption ents
    (HashMap.get core.cmp.EqI64 I64.Insts.CoreHashHash rsHasher
      (borrowSelf Std.I64) I64.Insts.CoreHashHash core.cmp.EqI64)

/-- `HashMap::insert` on the map of a `BlobMetaData`. -/
abbrev MetaInsertSpec (ents : MetaEntries) : Prop :=
  HashMapInsertAssumption ents
    (HashMap.insert core.cmp.EqI64 I64.Insts.CoreHashHash rsHasher)

/-- The metadata `m` is the metadata `m0` with the entries `new` added: the entries of `m` are
those of `new` and those of `m0` whose tag is not the tag of an entry of `new`. The tags are the
numbers that the macro in `database.rs` gives in declaration order: `EncryptedBy` 0, `Salt` 1,
`Iv` 2, `AeadTag` 3, `KmUuid` 4, `PublicKey` 5, `MaxBootLevel` 6. The list `new` has distinct
tags. -/
def MetaEntriesAre (ents : MetaEntries) (m0 m : database.BlobMetaData)
    (new : List (Std.I64 × database.BlobMetaEntry)) : Prop :=
  ∀ e, e ∈ ents m.data ↔ e ∈ new ∨ (e ∈ ents m0.data ∧ e.1 ∉ new.map Prod.fst)

/-! ## The super key manager -/

/-- A super key behind an `Arc`. -/
abbrev SuperKeyArc : Type := alloc.sync.Arc super_key.SuperKey

/-- Assumption about the clone of an `Arc` of a super key (register record
`ks2-ext-alloc-sync-arc-insts-corecloneclone-clone`). The call never panics and returns the same
`Arc`. Idealisation: the count of references does not overflow. -/
def ArcCloneSpec : Prop :=
  ∀ a : SuperKeyArc,
    CoreCloneClone.clone
      Insts.CoreAllocAllocatorClone a = ok a

/-- Assumption about `Option::cloned` at an `Arc` of a super key (register record
`ks2-ext-core-option-optionshared0t-cloned`). The call never panics and returns the same option:
the `Arc` inside is the same. Idealisation: the count of references does not overflow. -/
def OptionClonedArcSpec : Prop :=
  ∀ o : Option SuperKeyArc,
    OptionShared0T.cloned
      (Insts.CoreCloneClone super_key.SuperKey
        Insts.CoreAllocAllocatorClone) o = ok o

/-- The user keys: the entries of the map `user_keys` of the manager state. -/
abbrev UserKeyEntries : Type := Entries utils.AndroidUserId super_key.UserSuperKeys

/-- `HashMap::get` on `user_keys`. -/
abbrev UserKeysGetSpec (ents : UserKeyEntries) : Prop :=
  HashMapGetAssumption ents
    (HashMap.get Insts.CoreCmpEq
      Insts.CoreHashHash rsHasher (borrowSelf utils.AndroidUserId)
      Insts.CoreHashHash Insts.CoreCmpEq)

open super_key.SuperKeyManager.get_credential_encrypted_key_by_user_id_internal.closure.Insts
  renaming CoreOpsFunctionFnOnceTupleShared0UserSuperKeysOptionArcSuperKey → credentialFnOnce in
/-- `Option::and_then` at the call of `get_credential_encrypted_key_by_user_id_internal`. -/
abbrev CredentialAndThenSpec : Prop :=
  OptionAndThenAssumption credentialFnOnce (Option.and_then credentialFnOnce)

/-- The assumption for `Default::default` that makes the map `user_keys`. -/
abbrev UserKeysEmptySpec (ents : UserKeyEntries) : Prop :=
  HashMapDefaultAssumption ents
    (CoreDefaultDefault.default utils.AndroidUserId
      super_key.UserSuperKeys Insts.CoreDefaultDefault)

/-- The assumption for `Default::default` that makes the map `key_index`. -/
abbrev KeyIndexEmptySpec
    (ents : Entries Std.I64 (alloc.sync.Weak super_key.SuperKey alloc.alloc.Global)) : Prop :=
  HashMapDefaultAssumption ents
    (CoreDefaultDefault.default Std.I64
      (alloc.sync.Weak super_key.SuperKey alloc.alloc.Global)
      Insts.CoreDefaultDefault)

/-! ## Context calls -/

open core.result.Result.Insts.AnyhowContext in
open anyhow.context.ext.StdError renaming Blanket → StdBlanket in
open keystore2_crypto.error.Error.Insts renaming CoreErrorError → CryptoErrorError in
/-- A call `r.context("..")` with a `&str` message on a result that holds a `T` and a crypto
error. The root cause of the new error is the crypto error, and an `Ok` stays `Ok`. -/
abbrev CryptoStrCtxSpec (root : anyhow.Error → ErrRoot) (T : Type) : Prop :=
  ResultContextLaw (fun x => ErrRoot.crypto x) root
    (context (T := T) (StdBlanket CryptoErrorError)
      (Shared0T.Insts.CoreFmtDisplay Str.Insts.CoreFmtDisplay))

end Keystore2Verify.SuperKey
