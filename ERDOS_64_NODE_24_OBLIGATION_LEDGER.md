# Node [24] obligation ledger

## Frozen topology and corrected predecessor

The immutable Part-I edge is `[22] --no--> [24] --> [25]`.  The authoritative
finite predecessor is `runP13Node22FiniteDensityDecision`; its `withinCap`
constructor contains `VerifiedP13Node24FiniteDensityHandoff` on the identical
node-[21] packing.  Nodes [145]--[157] are the original Part-XI expansion
behind [22]--[24], not new proof-flow cases.

## Complete obligation ledger

| Task ID | Original-paper obligation/property | Current evidence | Status | Missing producer |
|---|---|---|---|---|
| 24.1 | Retain the exact `[22].withinCap` branch and identical node-[21] packing. | `VerifiedP13Node24FiniteDensityHandoff.previousExact` | proved | --- |
| 24.2 | Retain the corrected finite window cap with discarded-scale and powered-skeleton normalization errors explicit. | `thetaWindowWithError`, `thetaWindowCorrected` | proved | --- |
| 24.3 | Retain the exact sequential hot/cold payment on the same packing. | `sequentialHotColdAccounting` | proved | --- |
| 24.4 | Bound discarded scales by thirty per accepted hot owner. | `sequentialScaleLossBound` | proved | --- |
| 24.5 | Prove the full correction is `o(n log n)` and derive `theta <= theta_win + o(1)`. | `p13Node24NormalizationEnvelope_isLittleO`, `p13Node24ThetaError_tendsto_zero`, and `VerifiedP13Node24FiniteDensityHandoff.theta_le_thetaWindow_add_oOne` | proved | --- |
| 24.6 | Emit the sharper high-entropy proposition as the exact typed downstream obligation; do not prove node `[52]`'s joint-accounting conclusion at node `[24]`. | `P13Node24HighEntropyRequirement`, `p13Node24HighEntropyRequirement`, `P13Node24HighEntropyDownstreamRequirement` | proved | Node `[52]` remains responsible for discharging the carried proposition from its additional exact predecessors. |
| 24.7 | Derive the exact finite large-remainder connector with the same error. | `remainderCorrected` | proved | --- |
| 24.8 | Normalize the remainder connector to `|R| >= (1-13 theta_win)n-o(n)`. | `p13Node24RemainderError_tendsto_zero` and `VerifiedP13Node24FiniteDensityHandoff.remainder_ratio_ge_main_sub_oOne` | proved | --- |
| 24.9 | Prove the exact rational `tau_win` is below `1/4`. | `p13WindowTauExact_lt_quarter` | proved | --- |
| 24.10 | Transport the actual packing bound to `tau(theta) <= tau_win + o(1)`. | `p13Node24TauError_tendsto_zero`, `p13Node24Tau_denominator_eventually_positive`, and `VerifiedP13Node24FiniteDensityHandoff.tau_le_tauWindow_add_oOne` | proved | --- |
| 24.11 | Keep execution local and polynomial. | `localCheckCount_polynomial`; no new scan at node [24]. | proved | --- |

## Verdict

Node [24] is **11/11 proved** as a single-input/output diagram node. It consumes
the literal node-[22] no edge, proves the finite and asymptotic window/remainder
handoffs, and emits the exact typed high-entropy obligation. It does not claim
the later node-[52] joint-accounting theorem; that downstream consumer remains
yellow until its own additional predecessors and realization are proved.
