# Node [48] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[48]` |
| Incoming edge | `[47]` |
| Outgoing edge | `[49]` |
| Local responsibility | Convert the inherited full curvature rank and wedge floor into the exact finite forced-curvature cost, with the sharper coefficient under the inherited high-entropy premise. |
| Retained facts | Exact node-[47] full-rank leaf, node-[30] wedge supply, node-[21] counts, node-[19] surplus bound, node-[24] high-entropy premise when selected. |
| New output | Exact finite window/high-entropy inequalities and their curvature-cost forms. |
| Framework operation | `State.StageNode.mapFocusedBranchNoContinuation`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N48-PROV | Consume only node [47]'s literal full-rank leaf. | `[47]` | `Node48Stage`; `node48P13ForcedCurvatureCost` requires `Node47Stage` | `[49]` | kernel-checked |
| N48-CONSTANT | `c_Ω = log₂(543958/111286)` and the two exact wedge densities define the printed costs. | `[21]`, `[30]` | `node48CurvatureEntropyCost`; `node48WindowCurvatureDensity`; `node48HighEntropyCurvatureDensity` | `[49]` | kernel-checked |
| N48-FINITE | Transport the window wedge floor through node [34]'s full-rank inequality with the exact surplus error. | `[30]`, `[34]`, `[47]` | `Node48Output.finiteCost`; `Node34Output.fullRank` | `[49]` | kernel-checked |
| N48-HIGH | On the inherited node-[24] joint high-entropy premise, derive the sharper exact coefficient from the packing-density transformer and wedge supply. | `[24]`, `[30]`, `[34]`, `[47]` | `Node48Output.highEntropyFiniteCost` | `[49]` | kernel-checked |
| N48-COST | Convert both exact inequalities to curvature-cost units with the same explicit surplus error. | N48-FINITE, N48-HIGH | `node48ForcedCost_of_finiteCost`; `node48HighEntropyForcedCost_of_finiteCost` | `[49]` | kernel-checked |
| N48-ROUTE | Replace only the full-rank leaf payload; preserve node [20] and the closed rank-drop sibling. | framework | `mapFocusedBranchNoContinuation` | `[49]` | kernel-checked |
| N48-LOCAL | Use symbolic scalar transport only and enumerate no state, graph, support, or context family. | framework/paper arithmetic | `node48LocalChecks = 0` | `[49]` | kernel-checked |

## Status

All node-[48] obligations are proved on the literal node-[47] residual. The
finite integer inequalities and their real-valued cost transports are
kernel-checked, and the framework preserves every sibling without an
application-owned handoff.
