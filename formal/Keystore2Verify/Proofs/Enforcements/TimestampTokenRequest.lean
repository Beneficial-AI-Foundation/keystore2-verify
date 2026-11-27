import Keystore2Verify.Specs.Defs.Enforcements

namespace Keystore2Verify.Enforcements
open Aeneas Aeneas.Std Result keystore2
open std.sync.mpsc
open Keystore2Verify.Externals

/-- conditional: if the send on the channel succeeds, `timestamp_token_request` returns `()`. In the
Rust source this path does not log. Hypotheses: the outcome of `get_timestamp_token` (it returns
`r`) and of `Sender::send` of `r` (it returns `Ok`). -/
theorem timestamp_token_request_sent (challenge : utils.Challenge)
    (sender : Sender (TsResult))
    (r : TsResult)
    (hget : enforcements.get_timestamp_token challenge = ok r)
    (hsend : Sender.send sender r = ok (.Ok ())) :
    enforcements.timestamp_token_request challenge sender = ok () := by
  sorry

/-- conditional: if the receiver has hung up, `timestamp_token_request` returns `()`. In the Rust
source this path logs at the `info` level if that level is enabled. The result is `()` at every
logging level. Hypotheses: the outcomes of
`get_timestamp_token` (it returns `r`) and of `Sender::send` of `r` (it returns `Err e`); the shared
assumptions about the logging calls (`LogLevelPartialCmpSpec`, `LogMaxLevelSpec`, `LogLocSpec`,
`LogPrivateApiLogSpec`). -/
theorem timestamp_token_request_hung_up (challenge : utils.Challenge)
    (hcmp : LogLevelPartialCmpSpec) (hmax : LogMaxLevelSpec) (hloc : LogLocSpec)
    (hlog : LogPrivateApiLogSpec)
    (sender : Sender (TsResult))
    (r : TsResult)
    (e : SendError (TsResult))
    (hget : enforcements.get_timestamp_token challenge = ok r)
    (hsend : Sender.send sender r = ok (.Err e)) :
    enforcements.timestamp_token_request challenge sender = ok () := by
  sorry
