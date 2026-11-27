import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open error.Error.Insts.CoreConvertFromPostProcessorError
  renaming «from» → errorFromPostProcessor

/-- exact: `Error::from` of a `PostProcessorError` returns the `BinderTransaction` variant that
wraps its status. -/
theorem Error_from_post_processor (s : postprocessor_client.PostProcessorError) :
    errorFromPostProcessor s = ok (error.Error.BinderTransaction s) := by
  sorry

end Keystore2Verify.Error
