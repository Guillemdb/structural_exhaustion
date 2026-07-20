# Node [12] repair template

| Field | Value |
|---|---|
| Incoming edges | [11] -> [12] |
| Outgoing edges | [12] -> [13] |
| Local responsibility | Prove context-universality for target-complete identifications of the node-[11] boundaried atoms. |
| Retained facts | Literal node-[11] atom/profile stage and all earlier ledger facts. |
| New output | Context-universality certificate only. |
| CT chain | CT3 context-classification successor, framework-owned. |
| Immediate consumers | [13] |

## Obligations

| Task ID | Assertion | Producer | Evidence | Edge | Status |
|---|---|---|---|---|---|
| N12-PRED | Consume literal Node11Stage | [11] | `node12ContextUniversality` via `StageNode.mapStage` | [11]->[12] | proved |
| N12-QUERY | Use the exact node-[11] graph/atom scope | [11] | `Node11Context node11` in `Node12Output` | [11]->[12] | proved |
| N12-UNIV | Prove universality for target-complete identifications | [12] | `targetComplete_contextUniversal` | [12]->[13] | proved |
| N12-LEDGER | Append only universality fact | framework | `StageNode.mapStage` | downstream | proved |

Focused one-job kernel build passed through node [14].

Forbidden: bundling node [13] or using `ExactHandoff`/copied predecessor fields.
