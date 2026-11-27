import Keystore2Verify.Specs.Defs.LegacyBlob

namespace Keystore2Verify.LegacyBlob
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open legacy_blob.LegacyBlobLoader
/-- conditional: if the alias is not in the encoding of `encode_alias`, `decode_alias` returns an
error whose root cause is a `legacy_blob::Error` (class `other`). The input is not in the
encoding when the pure decoder `decodeNat` rejects its bytes. Hypotheses: the assumptions about
the byte iterator of a string, the message assumptions, and the assumption `ResultContextLaw`
about `context` for a `legacy_blob::Error`. -/
theorem decode_alias_bad_encoding (root : anyhow.Error → ErrRoot)
    (view : StrBytesIter → List Std.U8)
    (hbytes : StrBytesSpec view) (hnext : BytesNextSpec view) (hmsg : MessageSpecs)
    (hctx : LegacyErrCtxLaw root String) (nm : Str)
    (hbad : decodeNat none (nm.val.map (·.val)) [] = none) :
    ∃ e, decode_alias nm = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

/-- conditional: if the alias is in the encoding and the decoded bytes are valid UTF-8,
`decode_alias` returns the decoded string. The string has the bytes that the decoder `decodeNat`
produces. Hypotheses: the assumptions about the byte iterator of a string, about `from_utf8`, the
message assumptions, and the assumption `ResultContextLaw` about `context` for a
`FromUtf8Error`. -/
theorem decode_alias_ok (root : anyhow.Error → ErrRoot)
    (view : StrBytesIter → List Std.U8)
    (hbytes : StrBytesSpec view) (hnext : BytesNextSpec view) (hutf : StringFromUtf8Spec)
    (hmsg : MessageSpecs) (hctx : Utf8ErrCtxLaw root String) (nm : Str) (acc : List Nat)
    (hdec : decodeNat none (nm.val.map (·.val)) [] = some acc)
    (hvalid : ∃ s, (utf8Bytes s).map (·.val) = acc) :
    ∃ s, decode_alias nm = ok (.Ok s) ∧ (utf8Bytes s).map (·.val) = acc := by
  sorry

/-- conditional: if the alias is in the encoding but the decoded bytes are not valid UTF-8,
`decode_alias` returns an error whose root cause is a `FromUtf8Error` (class `other`).
Hypotheses: those of `decode_alias_ok`. -/
theorem decode_alias_invalid_utf8 (root : anyhow.Error → ErrRoot)
    (view : StrBytesIter → List Std.U8)
    (hbytes : StrBytesSpec view) (hnext : BytesNextSpec view) (hutf : StringFromUtf8Spec)
    (hmsg : MessageSpecs) (hctx : Utf8ErrCtxLaw root String) (nm : Str) (acc : List Nat)
    (hdec : decodeNat none (nm.val.map (·.val)) [] = some acc)
    (hvalid : ¬ ∃ s, (utf8Bytes s).map (·.val) = acc) :
    ∃ e, decode_alias nm = ok (.Err e) ∧ root e = ErrRoot.other := by
  sorry

end Keystore2Verify.LegacyBlob
