# Node [26] repair template

| Field | Value |
|---|---|
| Incoming | [25] -> [26] |
| Outgoing | [26] -> [27] |
| Responsibility | Attach the paper's exact remainder identity/first residual refinement. |
| Retained facts | Inherited through the accumulated ledger: literal Residual A and all previous facts. |
| New output | Node-26 local remainder identity only. |
| CT chain | Zero-copy framework successor. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N26-PRED | Consume literal Node25Stage | [25] | `node26P13RemainderContinuation` | kernel-checked, conditional |
| N26-IDENTITY | Prove exact local remainder identity | [26] | `Node26Output.canonicalRemainder` | kernel-checked, conditional |
| N26-LEDGER | Append identity without copying predecessor | framework | `State.StageNode.mapDependentDecisionOnNoYesClosedActive` | kernel-checked, conditional |

Forbidden: `ExactHandoff`, `previousExact`, or canonical recomputation.

Node [26] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. Its thin output is only the node-[26]
identity; the framework retains the predecessor. The node-local producer
showed no `sorryAx`.
