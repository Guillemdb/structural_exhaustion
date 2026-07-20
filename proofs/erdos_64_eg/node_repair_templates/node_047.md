# Node [47] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[47]` |
| Incoming edge | `[34]` (Part-II no-rank-drop leaf) |
| Outgoing edge | `[48]` |
| Local responsibility | Re-enter Part IV with the exact Residual B already named at node [34]. |
| Retained facts | Node-[32] no proof `r_Ω(R) ≥ W₂(R)-o(W₂)` and the complete accumulated ledger; Part-III terminal evidence is a sibling. |
| New output | None; this is the paper's literal cross-panel occurrence of the same leaf. |
| Framework operation | `State.StageNode.usingStage`, returning the retrieved `Node34Stage` unchanged. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N47-PROV | Consume exactly node [34]'s full-rank leaf, not node [46]'s rank-drop contradiction. | `[34]` | `Node47Stage := Node34Stage`; `node47P13FullRankContinuation` | `[48]` | kernel-checked, conditional |
| N47-RANK | Preserve the exact finite form of `r_Ω(R) ≥ W₂(R)-o(W₂)`. | `[32]`, `[34]` | the `Node32FullRank` proof is retained literally by the `Node34Stage` constructor | `[48]` | kernel-checked, conditional |
| N47-LEDGER | Keep all Part-III sibling terminals in the same accumulated ledger without treating them as this edge's mathematical input. | framework | `runInitialThroughNode47` extends `runInitialThroughNode46`; executor queries `Node34Stage` | `[48]` | kernel-checked, conditional |
| N47-THIN | Introduce no application payload, predecessor copy, handoff, or stronger exact-rank assertion. | framework alias | `Node47Stage` | `[48]` | kernel-checked, conditional |
| N47-WORK | Perform zero local checks. | framework | `node47LocalChecks = 0` | `[48]` | kernel-checked, conditional |

## Status

Partial with its local implementation kernel-checked; inherited missing
producers remain to be discharged.
Node [47] is deliberately not represented by the older stronger
`VerifiedP13Node47FullRankResidual` equality wrapper.
