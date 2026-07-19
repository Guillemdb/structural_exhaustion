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
| N11-PRED | Consume literal node-[10] stage | [10] | blocked: no `Node10Stage`/`node10Stage` declaration exists in the nodes [1]--[52] Lean cone | [10]->[11] | blocked |
| N11-QUERY | Retrieve only the inherited facts required by the atom definition | earlier ledger | blocked on N11-PRED; must use one `LedgerQuery` against the literal node-[10] ledger | [10]->[11] | blocked |
| N11-ATOMS | Define the exact paper-local boundaried atoms | [11] | graph primitives ready: `PackedBoundariedGluing.Piece` and `MinimumDegreeCycleReplacement.ProperAtom`; thin stage instantiation blocked on N11-PRED | [11]->[12] | blocked |
| N11-PROFILE | Construct the boundary-degree profile | [11] | graph primitive ready: `PackedBoundariedGluing.Piece.boundaryDegree`; thin payload must retain the full function on boundary labels; blocked on N11-PRED | [11]->[12] | blocked |
| N11-LEDGER | Append only the new atom/profile payload | framework | must be a framework `StageNode` successor of literal `Node10Stage`; blocked on N11-PRED | downstream | blocked |

## Framework and validation record

- Node [11] must not bundle nodes [12]--[14].
- No `ExactHandoff`, predecessor field, or all-boundaries future theorem is permitted.
- Dependency audit command: `rg -n --glob '*.lean' '\bNode10Stage\b|\bnode10Stage\b|Node10' examples/erdos_64_eg lean` (2026-07-19: no node-[10] stage declaration).
- Existing `Erdos64EG/CT3.lean` is not node-[11] evidence: it explicitly bundles nodes `[11]`--`[14]` and extends `Core.ExactHandoff`.
- Focused kernel command: blocked until the literal node-[10] stage exists; no node-[11] Lean module was authored.
- Dashboard/TeX synchronization: blocked; node [11] remains yellow.
