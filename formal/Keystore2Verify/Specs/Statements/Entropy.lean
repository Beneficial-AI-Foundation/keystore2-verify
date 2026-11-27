import Keystore2Verify.Proofs.Entropy.FeederInfo
import Keystore2Verify.Proofs.Entropy.GetEntropy

namespace Keystore2Verify.Entropy

section FeederInfo
open Aeneas Aeneas.Std Result keystore2
open android_hardware_security_keymint.aidl.android.hardware.security.keymint
open entropy.FeederInfo.Insts.CoreDefaultDefault renaming default → feederDefault
open std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault
  renaming default → hashMapDefault

recall feeder_info_default (hm : std.collections.hash.map.HashMap SecurityLevel.SecurityLevel
      std.time.Instant std.hash.random.RandomState alloc.alloc.Global)
    (h : hashMapDefault SecurityLevel.SecurityLevel std.time.Instant
      std.hash.random.RandomState.Insts.CoreDefaultDefault = ok hm) :
    feederDefault = ok { last_feed := hm }

end FeederInfo

section GetEntropy
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open keystore2_crypto.error.Error.Insts

recall get_entropy_ok (root : anyhow.Error → ErrRoot)
    (hctx : CryptoStrCtxAssumption root (alloc.vec.Vec Std.U8))
    (size : Std.Usize) (v : alloc.vec.Vec Std.U8)
    (h : keystore2_crypto.generate_random_data size = ok (.Ok v)) :
    entropy.get_entropy size = ok (.Ok v)

recall get_entropy_err (root : anyhow.Error → ErrRoot)
    (hctx : CryptoStrCtxAssumption root (alloc.vec.Vec Std.U8))
    (size : Std.Usize) (ce : keystore2_crypto.error.Error)
    (h : keystore2_crypto.generate_random_data size = ok (.Err ce)) :
    ∃ e, entropy.get_entropy size = ok (.Err e) ∧ root e = ErrRoot.crypto ce

end GetEntropy

end Keystore2Verify.Entropy
