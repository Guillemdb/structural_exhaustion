# Node [11] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [11] |
| Incoming edges | [10] -> [11] |
| Outgoing edges | [11] -> [12] |
| Local responsibility | Introduce the paper's boundaried atoms and their boundary-degree profiles. |
| Retained branch facts | Minimality, target avoidance, deletion criticality, and high-degree independence. |
| New output | The node-local boundaried-atom family and exact boundary-degree profile. |
| CT chain | CT3 graph profile initialization through a framework stage successor. |
| Immediate consumers | [12] |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N11-PRED | Consume literal node-[10] stage | [10] | `Node11Stage`, predecessor `Node10Stage` | [10]->[11] | implemented; check pending |
| N11-QUERY | Retrieve only the inherited facts required by the atom definition | earlier ledger | no inherited theorem is needed; `StageNode.mapStage` retrieves the literal `Node10Stage` | [10]->[11] | proved |
| N11-ATOMS | Define the exact paper-local boundaried atoms | [11] | `Node11ProperAtom`, `Node11BoundariedAtomFamily` | [11]->[12] | proved |
| N11-PROFILE | Construct the boundary-degree profile | [11] | `Node11AtomProfile`, `node11_boundaryDegreeProfile` | [11]->[12] | proved |
| N11-LEDGER | Append only the new atom/profile payload | framework | `node11BoundariedAtoms`, `runInitialThroughNode11` | downstream | proved |

## Framework and validation record

- Node [11] must not bundle nodes [12]--[14].
- No `ExactHandoff`, predecessor field, or all-boundaries future theorem is permitted.
- Literal predecessor: `Erdos64EG.Node10HighDegreeIndependence.Node10Stage`.
- Existing `Erdos64EG/CT3.lean` is not node-[11] evidence: it explicitly bundles nodes `[11]`--`[14]` and extends `Core.ExactHandoff`.
- Focused one-job kernel build passed through node [14].
- Trust output: `runInitialThroughNode11` and `node11_boundaryDegreeProfile` use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
- Dashboard/TeX synchronization: the node template and umbrella import now expose node [11] independently; generated dashboard refresh remains repository-level work.
