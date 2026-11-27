import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
/-- conditional: if the encoded alias has a known keystore prefix, `extract_legacy_alias` returns
`None`. In the Rust source this path returns before `decode_alias` is called. Hypothesis: the
outcome of `is_keystore_alias` (an item the extraction could not translate). -/
theorem extract_legacy_alias_prefixed (enc : Str) (his : is_keystore_alias enc = ok true) :
    extract_legacy_alias enc = ok none := by
  sorry

/-- conditional: if the encoded alias has no known keystore prefix and `decode_alias` returns
`Ok a`, `extract_legacy_alias` returns `Some a`. Hypotheses: the outcome of `is_keystore_alias`
and of `decode_alias`. -/
theorem extract_legacy_alias_decoded (enc : Str) (a : String)
    (his : is_keystore_alias enc = ok false) (hdec : decode_alias enc = ok (.Ok a)) :
    extract_legacy_alias enc = ok (some a) := by
  sorry

/-- conditional: if the encoded alias has no known keystore prefix and `decode_alias` returns an
error, `extract_legacy_alias` returns `None`: the error is dropped. Hypotheses: the outcome of
`is_keystore_alias` and of `decode_alias`. -/
theorem extract_legacy_alias_undecodable (enc : Str) (e : anyhow.Error)
    (his : is_keystore_alias enc = ok false) (hdec : decode_alias enc = ok (.Err e)) :
    extract_legacy_alias enc = ok none := by
  sorry

end Keystore2Verify.LegacyBlob
