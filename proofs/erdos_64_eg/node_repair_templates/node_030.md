# Node [30] repair template

| Field | Value |
|---|---|
| Incoming | [29] -> [30] |
| Outgoing | [30] -> [31] |
| Responsibility | Prove the paper's wedge lower bound for Residual A, with the sharper bound under the high-entropy premise. |
| Retained facts | Inherited through the accumulated ledger: node29 exact incidence supply and prior remainder/wedge identities. |
| New output | Window-only wedge floor and conditional high-entropy wedge floor. |
| CT chain | Framework finite-sum localization/arithmetic successor (CT11). |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N30-PRED | Consume literal Node29Stage | [29] | `node30P13WedgeLower` | kernel-checked, conditional |
| N30-COMPONENT | Prove the generic component wedge floor `3|C|-2def⁺(C)≤W₂(C)` | graph framework | `Node30Output.componentWedgeFloor` | kernel-checked, conditional |
| N30-REMAINDER | Specialize the wedge floor to the retained remainder | [30] | `Node30Output.remainderWedgeFloor` | kernel-checked, conditional |
| N30-FINITE | Combine node [29] with the remainder floor: `3|R|≤W₂(R)+30p13+2σ` | [29], [30] | `Node30Output.windowFiniteSupply` | kernel-checked, conditional |
| N30-DENSITY | Eliminate the exact packing density and retain the scaled surplus error | [24], [25], [30] | `Node30Output.windowFiniteError` | kernel-checked, conditional |
| N30-RATE | Prove the generic deficiency-rate to wedge-rate transport | graph framework | `Node30Output.rateTransport` | kernel-checked, conditional |
| N30-WINDOW | Certify the exact `τ_win`, `ω_win`, and printed lower coefficient `2.54365026308` | [30] | `node30WindowDeficiencyRate`; `node30OmegaWindow`; `node30OmegaWindow_gt_printed`; `Node30Output.windowRateTransport` | kernel-checked, conditional |
| N30-HIGH | Under the inherited high-entropy premise, prove the sharper `2.57407357888...` coefficient | [30] | `Node30Output.highEntropyTransport` | kernel-checked, conditional |
| N30-WORK | Retain the quadratic curvature-ledger work bound | graph framework | `Node30Output.localWork` | kernel-checked, conditional |
| N30-LEDGER | Append all implications once | framework | generic active-cursor map | kernel-checked, conditional |

Forbidden: deciding the high-entropy branch, proving curvature rank, or enumerating ambient graphs.

Node [30] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. It proves only the displayed finite floors
and conditional rate transport, and its thin output copies no predecessor
payload. The node-local producer showed no `sorryAx`.
