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
| N10-PRED | Consume literal node-[9] stage | [9] | pending | [9]->[10] | pending |
| N10-QUERY | Retrieve the node-[9] degree-three endpoint fact | [9] | pending | [9]->[10] | pending |
| N10-INDEP | Prove high-degree independence | [10] | existing theorem; attachment pending | [10]->[11] | partial |
| N10-ENTAILS | Register independence once | [10] | pending | downstream | pending |

## Framework and validation record

- Do not rederive deletion criticality from the graph context.
- Focused kernel command: pending.
- Dashboard/TeX synchronization: pending.
