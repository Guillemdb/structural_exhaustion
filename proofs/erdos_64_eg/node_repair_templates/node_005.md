# Node [5] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [5] |
| Incoming edges | [4] -> [5] |
| Outgoing edges | [5] -> [6] |
| Local responsibility | Establish the edge-rooted Mersenne-return target algebra for the selected counterexample. |
| Retained branch facts | Minimal counterexample and target avoidance. |
| New output | The reusable return/Mersenne equivalence attached to the ledger. |
| CT chain | CT1 target encoding/algebra through a framework successor. |
| Immediate consumers | [6] and later target-algebra consumers |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N5-PRED | Consume literal node-[4] stage | [4] | `Node5Stage`, `node5TargetAlgebra` | [4]->[5] | proved |
| N5-QUERY | Retrieve the minimal counterexample facts from the ledger | [4] | framework `StageNode.mapStage` retrieves `Node4Output` | [4]->[5] | proved |
| N5-ALG | Prove the exact return/Mersenne equivalence | [5] | `Node5TargetAlgebra.targetIffReturn`, `returnSetsDisjoint` | [5]->[6] | proved |
| N5-ENTAILS | Register the target proposition exactly once | [5] | `Node5TargetAlgebraFact`, `StageEntails Node5Stage` | downstream | proved |

## Framework and validation record

- No rederivation of minimality or target avoidance is permitted.
- The application supplies only the graph-specific target algebra.
- Focused kernel command: `lake build Erdos64EG.Node5TargetAlgebra`.
- Dashboard/TeX synchronization: pending.
