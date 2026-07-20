# Node [29] repair template

| Field | Value |
|---|---|
| Incoming | [28] -> [29] |
| Outgoing | [29] -> [30] |
| Responsibility | Prove the exact finite external-incidence supply inequalities for the retained remainder. |
| Retained facts | Inherited through the accumulated ledger: node28 deficiency identity and the selected P13 window/remainder surplus facts. |
| New output | Exact incidence ledger, `def⁺(R) ≤ 15 p13 + σ_W`, the signed surplus-adjusted consequence, and the finite near-cubic error certificate underlying `15 p13 + o(n)`. |
| CT chain | Framework deterministic charging/capacity successor (CT4). |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N29-PRED | Consume literal Node28Stage | [28] | `node29P13ExternalIncidenceSupply` | kernel-checked, conditional |
| N29-DEF-ID | Identify the curvature and deficiency ledgers | [28] | `Node29Output.deficiencyLedgerExact` | kernel-checked, conditional |
| N29-BOUNDARY | Bound positive deficiency by boundary incidences | [29] | `Node29Output.deficiency_le_boundaryIncidences` | kernel-checked, conditional |
| N29-TOKENS | Charge boundary incidences to packed-window tokens and prove `tokenCount = 15 p13 + σ_W` | [29] | `Node29Output.boundaryIncidences_le_windowTokens`; `Node29Output.tokenCountExact` | kernel-checked, conditional |
| N29-STUB | Deduce `def⁺(R) ≤ 15 p13 + σ_W` | [29] | `Node29Output.incidenceSupply` | kernel-checked, conditional |
| N29-PARTITION | Prove `σ_W+σ_R=σ` and `σ_W≤σ` | [29] | `Node29Output.surplusPartition`; `Node29Output.windowSurplus_le_total` | kernel-checked, conditional |
| N29-TOTAL | Deduce `def⁺(R) ≤ 15 p13 + σ` | [29] | `Node29Output.totalSurplusSupply` | kernel-checked, conditional |
| N29-SIGNED | Preserve the manuscript subtraction in `Int`: `def⁺(R)-σ_R ≤ 15p13+σ_W-σ_R` | [29] | `Node29Output.surplusAdjustedSupply` | kernel-checked, conditional |
| N29-ERROR | Use inherited node-[19] near-cubic control to prove `(def⁺(R)-15p13)^2 ≤ c n` | [19], [29] | `Node29Output.incidenceErrorSquared` | kernel-checked, conditional |
| N29-WORK | Retain the quadratic local window-ledger work bound | graph framework | `Node29Output.localWork` | kernel-checked, conditional |
| N29-LEDGER | Append all new consequences without copying predecessor payloads | framework | generic active-cursor map | kernel-checked, conditional |

Forbidden: curvature/wedge estimates, a second incidence ledger, or re-proving packing disjointness.

The exact square bound is node [29]'s finite producer for the displayed
`o(n)` error; conversion to asymptotic notation remains a later transport.
Node [29] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. Its thin output contains only the new
incidence consequences, not predecessor payloads. The node-local producer
showed no `sorryAx`.
