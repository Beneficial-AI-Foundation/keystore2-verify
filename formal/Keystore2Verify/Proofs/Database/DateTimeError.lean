import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.DateTimeError.Insts
open core.num.error
open CoreConvertFromSystemTimeError renaming «from» → dateTimeErrorFromSystemTime
open CoreConvertFromTryFromIntError renaming «from» → dateTimeErrorFromTryFromInt

/-- exact: `From<SystemTimeError>` never fails and wraps the error in `SystemTimeError`. -/
theorem date_time_error_from_system_time_error (e : std.time.SystemTimeError) :
    dateTimeErrorFromSystemTime e = ok (.SystemTimeError e) := by
  sorry

/-- exact: `From<TryFromIntError>` never fails and wraps the error in `TypeConversion`. -/
theorem date_time_error_from_try_from_int_error (e : TryFromIntError) :
    dateTimeErrorFromTryFromInt e = ok (.TypeConversion e) := by
  sorry
