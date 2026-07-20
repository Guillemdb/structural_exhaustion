# Node [25] repair template

| Field | Value |
|---|---|
| Incoming | [24] -> [25] |
| Outgoing | [25] -> [26] |
| Responsibility | Construct Residual A and prove it is large and componentwise P13-free. |
| Retained facts | Inherited through the accumulated ledger: exact node24 density bounds and maximal packing. |
| New output | Residual A with its two stated properties. |
| CT chain | Framework residual-refinement successor. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N25-PRED | Consume literal Node24Stage | [24] | `node25P13LargeRemainder` via `State.StageNode.mapDependentDecisionOnNoYesClosedActive` | kernel-checked, conditional |
| N25-RESIDUAL | Define exact graph remainder | [25] | `Node25Remainder`; `Node25Output.exactPartition` | kernel-checked, conditional |
| N25-LARGE | Prove exact scaled quantitative largeness | [24]/[25] | `Node25Output.scaledLarge`, derived symbolically from `Node24Output.windowDensity` and `p13Remainder_partition` | kernel-checked, conditional |
| N25-P13FREE | Prove remainder and componentwise P13-free | [17]/[25] | `Node25Output.remainderFree`; `Node25Output.componentwiseFree`, using `Graph.InducedPathPacking` theorems | kernel-checked, conditional |

Forbidden: ExactHandoff or copied node24 payload.

Node [25] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. Its thin output contains only the
node-[25] remainder facts; it does not copy the predecessor payload. The
node-local producer showed no `sorryAx`.
