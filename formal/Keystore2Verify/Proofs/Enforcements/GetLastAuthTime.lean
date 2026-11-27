import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open enforcements.Enforcements.get_last_auth_time.closure.Insts renaming
  CoreOpsFunctionFnTupleShared2AuthTokenEntryBool → lastAuthPredicate

/-- conditional: if the search for a token that satisfies `(sid, auth_type)` finds nothing,
`get_last_auth_time` returns `None`. Which entry the search picks lies in the per-boot database
item, which the translation leaves opaque (blocked by extraction). Hypothesis: the outcome of
`find_auth_token` with the predicate for `sid` and `auth_type` is `none`. -/
theorem get_last_auth_time_none (self : enforcements.Enforcements) (sid : utils.SecureUserId)
    (auth_type : AuthType)
    (hfind : enforcements.Enforcements.find_auth_token lastAuthPredicate (sid, auth_type)
      = ok none) :
    enforcements.Enforcements.get_last_auth_time self sid auth_type = ok none := by
  sorry

/-- conditional: if the search for a token that satisfies `(sid, auth_type)` finds the entry `e`,
`get_last_auth_time` returns `Some` of the time at which `e` was received. Hypothesis: the outcome
of `find_auth_token` with the predicate for `sid` and `auth_type` is `some e`. -/
theorem get_last_auth_time_some (self : enforcements.Enforcements) (sid : utils.SecureUserId)
    (auth_type : AuthType)
    (e : database.AuthTokenEntry)
    (hfind : enforcements.Enforcements.find_auth_token lastAuthPredicate (sid, auth_type)
      = ok (some e)) :
    enforcements.Enforcements.get_last_auth_time self sid auth_type
      = ok (some e.time_received) := by
  sorry
