# Node [9] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [9] |
| Incoming edges | [8] -> [9] |
| Outgoing edges | [9] -> [10] |
| Local responsibility | Establish edge-deletion criticality and that every edge touches a degree-three vertex. |
| Retained branch facts | Exact no-proper-core and minimal-counterexample certificates. |
| New output | The two paper-local deletion-criticality facts. |
| CT chain | CT2 local-deletion successor on the existing ledger. |
| Immediate consumers | [10] and later degree bookkeeping |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N9-PRED | Consume literal node-[8] stage | [8] | `Node9Stage`; `node9DeletionCriticality` via `StageNode.mapStage` | [8]->[9] | proved |
| N9-DELETE | Prove edge-deletion criticality | [9] | graph-owned `deletionCriticalityFacts`; thin `Node9Output` projection | [9]->[10] | proved |
| N9-DEG3 | Prove every edge touches degree three | [9] | `node9_everyEdgeTouchesDegreeThree` | [9]->[10] | proved |
| N9-LEDGER | Register the reusable fact once | framework | `StageEntails Node9DegreeThreeEndpointFact` | downstream | proved |

## Framework and validation record

- Erdős code must not mention route `OutputLedger` or CT transition internals.
- Focused kernel command: `cd examples/erdos_64_eg && lake -Kjobs=1 build Erdos64EG.Node14Uncompressibility` (passed through node [9]).
- Dashboard/TeX synchronization: outside this node-local repair slice.
