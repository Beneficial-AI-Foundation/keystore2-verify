import Keystore2Verify.Specs.Defs.Utils

namespace Keystore2Verify.Utils
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open libc.unix.linux_like.linux.gnu renaming PRIO_PROCESS → prioProcess,
  getpriority → libcGetpriority

/-- conditional: if `errno` reads 0 after the call, `getpriority` returns `Some r`, where `r` is
the value that the libc call `getpriority(PRIO_PROCESS, 0)` returned (any `i32`, also a negative
one). In the Rust source this path does not log. Hypotheses: `errno_clear` returns `()` (`hcl`),
`PRIO_PROCESS` is `ok p` (`hp`), the libc call returns `ok r` (`hr`), and `errno_read` returns 0
(`he`). -/
theorem getpriority_ok (p : Std.U32) (r : Std.I32)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcGetpriority p 0#u32 = ok r) (he : utils.errno_read = ok 0#i32) :
    utils.getpriority = ok (some r) := by
  sorry

/-- conditional: if `errno` reads a value other than 0 after the call, `getpriority` returns
`None`. In the Rust source it first logs a warning, which does not change the result.
Hypotheses: as for `getpriority_ok`, but `errno_read` returns `e` with `e ≠ 0` (`he`, `hne`),
and the shared assumptions about the logging calls (`max_level`, the comparison of `Level`
with `LevelFilter`, `loc` and `log`). -/
theorem getpriority_errno (p : Std.U32) (r e : Std.I32)
    (hmax : LogMaxLevelSpec) (hcmp : LogLevelPartialCmpSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcGetpriority p 0#u32 = ok r) (he : utils.errno_read = ok e) (hne : e ≠ 0#i32) :
    utils.getpriority = ok none := by
  sorry

/-- conditional: if `errno_clear` fails with `e`, `getpriority` fails with `e`. Hypothesis: the
outcome of the opaque call (`hcl`). -/
theorem getpriority_fail_clear (e : Error) (hcl : utils.errno_clear = fail e) :
    utils.getpriority = fail e := by
  sorry

/-- conditional: if `errno_clear` returns `()` and the constant `PRIO_PROCESS` fails with `e`,
`getpriority` fails with `e`. Hypotheses: `hcl`, `hp`. -/
theorem getpriority_fail_prio (e : Error) (hcl : utils.errno_clear = ok ())
    (hp : prioProcess = fail e) : utils.getpriority = fail e := by
  sorry

/-- conditional: if the first two calls return normally and the libc call `getpriority` fails with
`e`, `getpriority` fails with `e`. Hypotheses: `hcl`, `hp` (`PRIO_PROCESS` is `ok p`), `hr`. -/
theorem getpriority_fail_libc (p : Std.U32) (e : Error) (hcl : utils.errno_clear = ok ())
    (hp : prioProcess = ok p) (hr : libcGetpriority p 0#u32 = fail e) :
    utils.getpriority = fail e := by
  sorry

/-- conditional: if the first three calls return normally and `errno_read` fails with `e`,
`getpriority` fails with `e`. Hypotheses: `hcl`, `hp`, `hr` (the libc call returns `ok r`), `he`. -/
theorem getpriority_fail_errno (p : Std.U32) (r : Std.I32) (e : Error)
    (hcl : utils.errno_clear = ok ()) (hp : prioProcess = ok p)
    (hr : libcGetpriority p 0#u32 = ok r) (he : utils.errno_read = fail e) :
    utils.getpriority = fail e := by
  sorry

end Keystore2Verify.Utils
