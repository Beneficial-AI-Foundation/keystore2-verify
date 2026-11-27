import Keystore2Verify.Specs.Defs.Error

namespace Keystore2Verify.Error
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals

/-- exact: `log_client_error` with no level returns `()`. In the Rust source this path returns
before `AppUid::calling` is called. -/
theorem log_client_error_none (e : anyhow.Error) :
    error.log_client_error none e = ok () := by
  sorry

/-- conditional: `log_client_error` with a level returns `()`. In the Rust source the calling uid
is read and, if the level passes the log filters, one record is logged. Hypotheses: the call that
reads the calling uid returns `ok u`, and the four assumptions about logging. -/
theorem log_client_error_some (l : log.Level) (e : anyhow.Error) (u : Std.U32)
    (huid : binder.ThreadState.get_calling_uid = ok u)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec) :
    error.log_client_error (some l) e = ok () := by
  sorry

end Keystore2Verify.Error
