import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open libc.unix.linux_like.linux.gnu renaming PRIO_PROCESS → prioProcess,
  setpriority → libcSetpriority

/-- conditional: if the libc call `setpriority(PRIO_PROCESS, 0, prio)` returns 0, `setpriority`
returns `()`. In the Rust source this path does not read `errno` and does not log.
Hypotheses: `errno_clear` returns `()` (`hcl`), `PRIO_PROCESS` is `ok p` (`hp`), and the libc
call returns 0 (`hr`). -/
theorem setpriority_ok (prio : Std.I32) (p : Std.U32)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = ok 0#i32) :
    utils.setpriority prio = ok () := by
  sorry

/-- conditional: if the libc call returns a value other than 0, `setpriority` still returns `()`:
the failure is only logged, and is not returned. Hypotheses: as for `setpriority_ok`, but the
libc call returns `r` with `r ≠ 0` (`hr`, `hne`); `errno_read` returns `e` (`he`); and the shared
assumptions about the logging calls (`max_level`, the comparison of `Level` with `LevelFilter`,
`loc` and `log`). -/
theorem setpriority_failed (prio : Std.I32) (p : Std.U32) (r e : Std.I32)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = ok r) (hne : r ≠ 0#i32)
    (he : utils.errno_read = ok e) :
    utils.setpriority prio = ok () := by
  sorry

/-- conditional: if `errno_clear` fails with `e`, `setpriority` fails with `e`. Hypothesis: the
outcome of the opaque call (`hcl`). -/
theorem setpriority_fail_clear (prio : Std.I32) (e : Error) (hcl : utils.errno_clear = fail e) :
    utils.setpriority prio = fail e := by
  sorry

/-- conditional: if `errno_clear` returns `()` and the constant `PRIO_PROCESS` fails with `e`,
`setpriority` fails with `e`. Hypotheses: `hcl`, `hp`. -/
theorem setpriority_fail_prio (prio : Std.I32) (e : Error) (hcl : utils.errno_clear = ok ())
    (hp : prioProcess = fail e) : utils.setpriority prio = fail e := by
  sorry

/-- conditional: if the first two calls return normally and the libc call `setpriority` fails
with `e`, `setpriority` fails with `e`. Hypotheses: `hcl`, `hp` (`PRIO_PROCESS` is `ok p`), `hr`. -/
theorem setpriority_fail_libc (prio : Std.I32) (p : Std.U32) (e : Error)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = fail e) : utils.setpriority prio = fail e := by
  sorry

/-- conditional: if the libc call returns a value other than 0 and `errno_read` fails with `e`,
`setpriority` fails with `e`. In the Rust source this path returns before logging. Hypotheses:
`hcl`, `hp`, `hr` (the libc call returns `ok r` with `r ≠ 0`), `he`. -/
theorem setpriority_fail_errno (prio : Std.I32) (p : Std.U32) (r : Std.I32) (e : Error)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcSetpriority p 0#u32 prio = ok r) (hne : r ≠ 0#i32)
    (he : utils.errno_read = fail e) : utils.setpriority prio = fail e := by
  sorry

end Keystore2Verify.Utils
