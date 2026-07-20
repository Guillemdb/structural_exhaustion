# Node [10] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [10] |
| Incoming edges | [9] -> [10] |
| Outgoing edges | [10] -> [11] |
| Local responsibility | Prove that vertices of degree at least four form an independent set. |
| Retained branch facts | Edge-deletion criticality and the degree-three endpoint property. |
| New output | High-degree independence. |
| CT chain | Thin graph-local framework successor. |
| Immediate consumers | [11] and later surplus bookkeeping |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N10-PRED | Consume literal node-[9] stage | [9] | `Node10Stage`; `node10HighDegreeIndependence` | [9]->[10] | proved |
| N10-QUERY | Consume the node-[9] degree-three endpoint fact | [9] | literal predecessor payload `node9.output` | [9]->[10] | proved |
| N10-INDEP | Prove high-degree independence | [10] | `Node10HighDegreeIndependentFact`; `node10_highDegreeVerticesIndependent` | [10]->[11] | proved |
| N10-ENTAILS | Register independence once | [10] | `StageEntails Node10Stage Node10HighDegreeIndependentFact` | downstream | proved |

## Framework and validation record

- Deletion criticality is not rederived from the graph context; the graph-local
  successor theorem consumes the endpoint proposition queried from node `[9]`.
- Focused one-job kernel build passed through node [14].
- Dashboard/TeX synchronization: pending.
