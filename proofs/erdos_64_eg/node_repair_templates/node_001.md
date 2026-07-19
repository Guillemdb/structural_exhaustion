# Node [1] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [1] |
| Incoming edges | theorem root |
| Outgoing edges | [1] -> [2] |
| Local responsibility | Introduce the finite simple graph quantified by the official theorem. |
| Retained branch facts | None; this is the genuine root. |
| New output | Root graph stage. |
| CT chain | `StageNode.exact` is permitted only here. |
| Immediate consumers | [2] |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N1-GRAPH | Introduce the exact official graph | theorem binder | `OfficialStatement` | [1]->[2] | proved |
| N1-ROOT | Seed the unique accumulated ledger once | [1] | `runInitialCounterexampleDecision` | [1]->[2] | proved |

## Framework and validation record

- Permitted exceptional operation: the sole root `StageNode.exact`.
- Forbidden: any second seed, application route, handoff, or copied graph field downstream.
- Focused kernel command: `lake env lean Erdos64EG/InternalProblem.lean` passed.
- Dashboard/TeX synchronization: pending batch check.
