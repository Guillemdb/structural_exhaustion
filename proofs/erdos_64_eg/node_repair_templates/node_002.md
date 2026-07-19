# Node [2] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [2] |
| Incoming edges | [1] -> [2] |
| Outgoing edges | no -> [3]; yes -> [4] |
| Local responsibility | Decide whether the graph has minimum degree at least three and avoids every power-of-two cycle. |
| Retained branch facts | Exact graph from [1]. |
| New output | Exhaustive yes/no counterexample certificate. |
| CT chain | Framework dependent decision on the root stage. |
| Immediate consumers | [3], [4] |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N2-PRED | Consume literal node-[1] root stage | [1] | `runInitialCounterexampleDecision` | [1]->[2] | proved |
| N2-PREDICATE | Use the exact paper counterexample predicate | [2] | `IsCounterexample` / `CounterexampleBranch.Yes` | both | proved |
| N2-DECIDE | Produce an exhaustive dependent decision | [2] | `CounterexampleBranch.decision` | both | proved |
| N2-LEDGER | Append the exact branch proposition to the one ledger | [2] | `CounterexampleBranch.run` | both | proved |
| N2-WORK | Retain local decision work evidence | framework | proof-level complement decision, zero local enumeration | both | proved |

## Framework and validation record

- Input query: root graph only.
- Application output: no custom structure; use the framework decision branches.
- Forbidden: caller-selected counterexample branch or application sum/route.
- Focused kernel commands: `lake build StructuralExhaustion.Core.CounterexampleBranch`; `lake env lean Erdos64EG/InternalProblem.lean` passed.
- Dashboard/TeX synchronization: pending.
