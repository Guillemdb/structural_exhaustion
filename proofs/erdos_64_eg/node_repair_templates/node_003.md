# Node [3] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [3] |
| Incoming edges | [2] no -> [3] |
| Outgoing edges | branch terminal |
| Local responsibility | Convert the exact negative counterexample branch into the official conclusion for this graph. |
| Retained branch facts | Graph, baseline, and `¬ IsCounterexample G` from [2]. |
| New output | Branch-local official conclusion. |
| CT chain | Framework continuation of node [2]'s no-stage. |
| Immediate consumers | terminal only |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N3-PRED | Consume literal node-[2] no-stage | [2] | `CounterexampleBranch.run` no branch | no->[3] | proved |
| N3-QUERY | Retrieve graph, baseline, and negative certificate from its ledger | [1],[2] | stable root residual plus literal latest no proof | no->[3] | proved |
| N3-CLOSE | Derive the official graph conclusion | [3] | `CounterexampleBranch.run` / `target_of_not_isCounterexample` | terminal | proved |
| N3-WORK | Record zero-copy continuation work | framework | `BranchResult.mapNo` proof-only continuation | terminal | proved |

## Framework and validation record

- No caller may supply `notCounterexample` or the conclusion.
- The node closes only node [2]'s no branch.
- Focused kernel commands: `lake build StructuralExhaustion.Core.CounterexampleBranch`; `lake env lean Erdos64EG/InternalProblem.lean` passed.
- Dashboard/TeX synchronization: pending.
