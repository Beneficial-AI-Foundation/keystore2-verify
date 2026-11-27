import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.SuperEncryptionAlgorithm.Insts renaming
  CoreCloneClone → algorithmClone, CoreCmpPartialEqSuperEncryptionAlgorithm → algorithmEq

/-- exact: `clone` on `SuperEncryptionAlgorithm` never fails and returns its argument. -/
theorem SuperEncryptionAlgorithm_clone (a : super_key.SuperEncryptionAlgorithm) :
    algorithmClone.clone a = ok a := by
  sorry

/-- exact: `==` on `SuperEncryptionAlgorithm` never fails and returns `true` exactly when both
arguments are the same variant (`Aes256Gcm` or `EcdhP521`). -/
theorem SuperEncryptionAlgorithm_eq (a b : super_key.SuperEncryptionAlgorithm) :
    ∃ r, algorithmEq.eq a b = ok r ∧ (r = true ↔ a = b) := by
  sorry

end Keystore2Verify.SuperKey
