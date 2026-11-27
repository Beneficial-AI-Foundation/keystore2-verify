import Keystore2Verify.Specs.Defs.Externals

namespace Keystore2Verify.RawDevice
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open raw_device.KeyMintDevice renaming
  internal_descriptor → internalDescriptor, lookup_from_desc → lookupFromDesc
open raw_device.KeyMintDevice.lookup_from_desc.closure.Insts
  renaming CoreOpsFunctionFnPairShared0KeyDescriptorOptionKeyPermSetResultTupleError → lookupCheck
open database.KeystoreDB renaming load_key_entry → loadKeyEntry

/-- conditional: `internal_descriptor alias` returns the key descriptor with the domain `APP`, the
namespace `AID_KEYSTORE`, the alias `alias` and no blob. The namespace is the external constant
`rustutils::android::users::AID_KEYSTORE` (`k`) converted to an `i64` (the value is kept).
Hypotheses: the external constant `AID_KEYSTORE` is `k`, and `Domain::APP` is `d`. -/
theorem internal_descriptor_value (k : Std.U32)
    (hk : rustutils.android.users.AID_KEYSTORE = ok k) (d : Domain.Domain)
    (hd : Domain.Domain.APP = ok d) (alias_ : String) :
    ∃ au, internalDescriptor alias_ =
        ok { domain := d, nspace := au, «alias» := some alias_, blob := none } ∧
      au.val = k.val := by
  sorry

/-- conditional: if `load_key_entry` (with the load bits `KM`, as `AID_KEYSTORE`, and a permission
check that always succeeds) returns an entry, `lookup_from_desc` returns it, and the database that
`load_key_entry` returned. Hypotheses: the external constant `AID_KEYSTORE` is `k`, passed as an
`i64` (the value is kept), and the outcome of `load_key_entry` (a database read that may sleep and
retry); `format` and `from_str_nonconst` do not fail; the assumption about `context` for an
`anyhow::Error` (`AnyCtxLaw`). -/
theorem lookup_from_desc_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (db db1 : database.KeystoreDB) (key_desc : KeyDescriptor.KeyDescriptor)
    (key_type : database.KeyType) (k : Std.U32)
    (hk : rustutils.android.users.AID_KEYSTORE = ok k)
    (v : database.KeyIdGuard × database.KeyEntry)
    (hload : loadKeyEntry lookupCheck db key_desc key_type database.KeyEntryLoadBits.KM
      (UScalar.hcast .I64 k) () =
      ok (.Ok v, db1)) :
    lookupFromDesc db key_desc key_type = ok (.Ok v, db1) := by
  sorry

/-- conditional: if `load_key_entry` returns an error `e`, `lookup_from_desc` returns an error with
the same root cause, and the database that `load_key_entry` returned. Hypotheses: the external
constant `AID_KEYSTORE` is `k`, passed as an `i64` (the value is kept), and the outcome of
`load_key_entry`; `format` and `from_str_nonconst` do not fail; the assumption about `context` for
an `anyhow::Error` (`AnyCtxLaw`). -/
theorem lookup_from_desc_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (db db1 : database.KeystoreDB) (key_desc : KeyDescriptor.KeyDescriptor)
    (key_type : database.KeyType) (k : Std.U32)
    (hk : rustutils.android.users.AID_KEYSTORE = ok k)
    (e : anyhow.Error)
    (hload : loadKeyEntry lookupCheck db key_desc key_type database.KeyEntryLoadBits.KM
      (UScalar.hcast .I64 k) () =
      ok (.Err e, db1)) :
    ∃ e', lookupFromDesc db key_desc key_type = ok (.Err e', db1) ∧ root e' = root e := by
  sorry
