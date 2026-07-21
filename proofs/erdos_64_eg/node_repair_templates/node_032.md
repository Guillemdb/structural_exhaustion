# Node [32] repair template

| Field | Value |
|---|---|
| Incoming | [31] -> [32] |
| Outgoing | yes -> [33]; no -> [34] |
| Responsibility | Execute the exact CT15 strict-loss/full-cardinality dichotomy on node [31]'s curvature target-rank. |
| Retained facts | Literal node-[31] support-stratified rank profile and the full accumulated ledger. |
| New output | Exact `Node32RankDrop : rΩ < |W₂|` or complementary `Node32FullRank : rΩ = |W₂|`; no branch conclusion. |
| CT chain | CT15 `rankDecision` through Core's focused dependent-decision executor. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N32-PRED | Consume the literal node-[31] stage | [31] | `node32P13RankDropDecision`; `runInitialThroughNode32` | kernel-checked, conditional |
| N32-RANK-DROP | Retain CT15's strict declared-coordinate rank-loss constructor | [32] | `Node32RankDrop`; `node32RankDecision` | kernel-checked, conditional |
| N32-FULL | Retain CT15's exact full-cardinality constructor | [32] | `Node32FullRank`; `node32RankDecision_exhaustive` | kernel-checked, conditional |
| N32-DECIDE | Route both literal residuals while preserving the one ledger | framework/[32] | `Node32Stage`; `node32P13RankDropDecision` | kernel-checked, conditional |
| N32-WORK | Record the proof-level CT15 split's zero finite scans | [32] | `node32LocalChecks_eq_zero`; `node32RankDecisionWork_eq_zero` | kernel-checked, conditional |

The exact finite full-cardinality constructor is stronger than the displayed
asymptotic lower bound.  The strict constructor is consumed by Branch D; its
support-stratified circuit is extracted at node [35]. Forbidden: proving
full-rank curvature cost, closing either branch, or enumerating quotient or
support families.

Node [32] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. The node-local producer showed no
`sorryAx`; no focused-validation task remains.
