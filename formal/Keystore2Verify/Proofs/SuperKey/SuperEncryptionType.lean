import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.SuperEncryptionType.Insts renaming CoreCloneClone → typeClone

/-- exact: `clone` on `SuperEncryptionType` never fails and returns its argument, for every
variant. The level of `BootLevel(l)` is copied. -/
theorem SuperEncryptionType_clone (t : super_key.SuperEncryptionType) :
    typeClone.clone t = ok t := by
  sorry

end Keystore2Verify.SuperKey
