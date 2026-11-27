import Keystore2Verify.Proofs.RawDevice.KeyMintDevice

namespace Keystore2Verify.RawDevice

section KeyMintDevice
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open android_system_keystore2.aidl.android.system.keystore2
open raw_device.KeyMintDevice renaming
  internal_descriptor → internalDescriptor, lookup_from_desc → lookupFromDesc
open raw_device.KeyMintDevice.lookup_from_desc.closure.Insts
  renaming CoreOpsFunctionFnPairShared0KeyDescriptorOptionKeyPermSetResultTupleError → lookupCheck
open database.KeystoreDB renaming load_key_entry → loadKeyEntry

recall internal_descriptor_value (k : Std.U32)
    (hk : rustutils.android.users.AID_KEYSTORE = ok k) (d : Domain.Domain)
    (hd : Domain.Domain.APP = ok d) (alias_ : String) :
    ∃ au, internalDescriptor alias_ =
        ok { domain := d, nspace := au, «alias» := some alias_, blob := none } ∧
      au.val = k.val

recall lookup_from_desc_ok (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (db db1 : database.KeystoreDB) (key_desc : KeyDescriptor.KeyDescriptor)
    (key_type : database.KeyType) (k : Std.U32)
    (hk : rustutils.android.users.AID_KEYSTORE = ok k)
    (v : database.KeyIdGuard × database.KeyEntry)
    (hload : loadKeyEntry lookupCheck db key_desc key_type database.KeyEntryLoadBits.KM
      (UScalar.hcast .I64 k) () =
      ok (.Ok v, db1)) :
    lookupFromDesc db key_desc key_type = ok (.Ok v, db1)

recall lookup_from_desc_err (root : anyhow.Error → ErrRoot)
    (hfmt : AllocFmtFormatSpec) (hstr : CoreFmtArgumentsFromStrNonconstSpec)
    (hany : AnyCtxLaw root (database.KeyIdGuard × database.KeyEntry))
    (db db1 : database.KeystoreDB) (key_desc : KeyDescriptor.KeyDescriptor)
    (key_type : database.KeyType) (k : Std.U32)
    (hk : rustutils.android.users.AID_KEYSTORE = ok k)
    (e : anyhow.Error)
    (hload : loadKeyEntry lookupCheck db key_desc key_type database.KeyEntryLoadBits.KM
      (UScalar.hcast .I64 k) () =
      ok (.Err e, db1)) :
    ∃ e', lookupFromDesc db key_desc key_type = ok (.Err e', db1) ∧ root e' = root e

end KeyMintDevice

end Keystore2Verify.RawDevice
