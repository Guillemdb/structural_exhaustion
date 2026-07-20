# Node [49] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[49]` |
| Incoming edge | `[48]` |
| Outgoing edge | `[50]` |
| Local responsibility | Define the paper's constrained labelled remainder family `𝒢(R)` and its per-vertex entropy `η(R)=log₂|𝒢(R)|/|R|`. |
| Retained facts | Exact fixed remainder and all already imposed branch constraints; node-[48] cost remains accumulated but is not re-proved. |
| New output | The exact symbolic entropy identity for that family. |
| Framework operation | `State.StageNode.mapActiveCursorDecisionNoContinuation`; graph family is `Graph.ConstrainedLabelledGraphFamily.Profile`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N49-PROV | Consume the literal node-[48] full-rank payload. | `[48]` | `node49P13RemainderEntropy` requires and maps the exact `Node48Stage` leaf | `[50]` | kernel-checked, conditional |
| N49-CARRIER | Every candidate is a labelled simple graph on the fixed remainder vertex set. | `[25]`--`[27]` | `P13RemainderVertex`; `node49RemainderGraphFamilyProfile` | `[50]` | kernel-checked, conditional |
| N49-CONSTRAINTS | The family predicate is exactly: subcubic atom part, componentwise `P₁₃`-free, no internal 3-core, and net-deficiency at the inherited cap. | earlier remainder ledger | `node49RemainderGraphAdmissible` | `[50]` | kernel-checked, conditional |
| N49-FINITE | The predicate-defined family is finite symbolically, with no graph list or universe scan. | graph framework | `ConstrainedLabelledGraphFamily.Profile.State`; `stateCount` | `[50]` | kernel-checked, conditional |
| N49-ENTROPY | `η(R)=log₂|𝒢(R)|/|R|`. | local definition | `node49RemainderEntropy`; `Node49Output.entropyExact` | `[50]` | kernel-checked, conditional |
| N49-ROUTE | Replace only node [48]'s live leaf and preserve both handled siblings. | framework | `mapActiveCursorDecisionNoContinuation` | `[50]` | kernel-checked, conditional |
| N49-WORK | The node is symbolic bookkeeping with zero semantic scans. | graph/core | `Node49Output.semanticChecksZero`; `node49LocalChecks = 0` | `[50]` | kernel-checked, conditional |

## Status

Partial with its local implementation kernel-checked; inherited missing
producers remain to be discharged.
Node [49] does not assert simultaneous realization, a high-entropy bit lower
bound, a dominant local type, or any node-[52] joint accounting theorem.
