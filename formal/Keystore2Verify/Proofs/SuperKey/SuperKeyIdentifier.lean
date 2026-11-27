import Keystore2Verify.Specs.Defs.SuperKey

namespace Keystore2Verify.SuperKey
open Aeneas Aeneas.Std Result keystore2 Keystore2Verify.Externals Keystore2Verify.Globals

open super_key.SuperKeyIdentifier.Insts renaming CoreCloneClone → identifierClone

/-- exact: `clone` on `SuperKeyIdentifier` never fails and returns its argument, for both
variants (`DatabaseId` and `BootLevel`). -/
theorem SuperKeyIdentifier_clone (i : super_key.SuperKeyIdentifier) :
    identifierClone.clone i = ok i := by
  sorry

end Keystore2Verify.SuperKey
