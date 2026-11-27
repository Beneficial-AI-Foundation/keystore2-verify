import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader

/-- conditional: if the closure returns `Ok v`, `with_retry_interrupted` returns `Ok v`.
Hypothesis: the outcome of the call of the closure `f`. -/
theorem with_retry_interrupted_ok {F T : Type}
    (inst : RetryFn F T)
    (f : F) (v : T) (h : inst.call f () = ok (.Ok v)) :
    with_retry_interrupted inst f = ok (.Ok v) := by
  sorry

/-- conditional: if the closure returns `Err e` and the kind of `e` is not `Interrupted`,
`with_retry_interrupted` returns `Err e` after that one call. Hypotheses: the outcome of the call of
the closure `f` and the kind of the error. The case of the kind `Interrupted` has no statement: the
Rust source calls the closure again, and a theorem cannot say that a second call returns another
result than the first. -/
theorem with_retry_interrupted_err {F T : Type}
    (inst : RetryFn F T)
    (f : F) (e : IoError) (k : IoErrorKind)
    (h : inst.call f () = ok (.Err e)) (hk : ioErrorKind e = ok k)
    (hne : k ≠ ioInterrupted) :
    with_retry_interrupted inst f = ok (.Err e) := by
  sorry

end Keystore2Verify.LegacyBlob
