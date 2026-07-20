# Node [48] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[48]` |
| Incoming edge | `[47]` |
| Outgoing edge | `[49]` |
| Local responsibility | Convert the inherited full curvature rank and wedge floor into the exact finite forced-curvature cost, with the sharper conditional high-entropy coefficient. |
| Retained facts | Exact node-[47] full-rank leaf, node-[30] wedge supply, node-[21] counts, node-[19] surplus bound, node-[24] high-entropy premise when selected. |
| New output | Exact finite window/high-entropy inequalities and their curvature-cost forms. |
| Framework operation | `State.StageNode.mapActiveCursorDecisionNoContinuation`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N48-PROV | Consume only node [47]'s literal full-rank leaf. | `[47]` | `Node48Stage`; `node48P13ForcedCurvatureCost` requires `Node47Stage` | `[49]` | kernel-checked, conditional |
| N48-CONSTANT | `c_Ω = log₂(543958/111286)` and the two exact wedge densities define the printed costs. | `[21]`, `[30]` | `node48CurvatureEntropyCost`; `node48WindowCurvatureDensity`; `node48HighEntropyCurvatureDensity` | `[49]` | kernel-checked, conditional |
| N48-FINITE | Transport the window wedge floor through full rank with the exact surplus error. | `[30]`, `[47]` | `Node48Output.finiteCost` | `[49]` | missing finite producer; conditional transport proved |
| N48-HIGH | On the inherited node-[24] joint high-entropy premise, prove the sharper exact coefficient. | `[24]`, `[30]`, `[47]` | `Node48Output.highEntropyFiniteCost` | `[49]` | missing finite producer; conditional transport proved |
| N48-COST | Convert both exact inequalities to curvature-cost units with the same explicit surplus error. | N48-FINITE, N48-HIGH | `node48ForcedCost_of_finiteCost`; `node48HighEntropyForcedCost_of_finiteCost` | `[49]` | kernel-checked, conditional |
| N48-ROUTE | Replace only the full-rank leaf payload; preserve node [20] and the closed rank-drop sibling. | framework | `mapActiveCursorDecisionNoContinuation` | `[49]` | kernel-checked, conditional |
| N48-LOCAL | Use symbolic scalar transport only and enumerate no state, graph, support, or context family. | framework/paper arithmetic | `node48LocalChecks = 0` | `[49]` | kernel-checked, conditional |

## Status

Yellow with the local adapter and both scalar cost transports kernel-checked.
The missing finite producer is exactly indexed by the node-[34]/[47] full-rank
leaf and now supplies only the two finite integer accounting inequalities;
the real-valued cost conclusions are derived locally.  Its remaining
node-[30]/node-[24] accumulated-ledger retrieval is never green evidence and
adds no diagram node, edge, or branch.
