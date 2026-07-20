# Node [50] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[50]` |
| Incoming edge | `[49]` |
| Outgoing edges | yes `[51]`; no `[53]` |
| Local responsibility | Decide exactly whether `η(R) ≥ (1/10) log₂ n`. |
| Retained facts | Literal node-[49] family and entropy identity on the full-rank leaf; every earlier ledger fact. |
| New output | Exhaustive high/strict-low ordered comparison for that same entropy value. |
| Framework operation | `State.StageNode.decideActiveCursorDecisionNoContinuation` with `Core.OrderThresholdSplit.Profile ℝ`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N50-PROV | Focus only node [49]'s literal full-rank active leaf. | `[49]` | `Node50Active`; `node50P13EntropyDecision` requires `Node49Stage` | both | kernel-checked, conditional |
| N50-THRESHOLD | The threshold is exactly `(1/10) log₂ n` on the same fixed graph order. | paper definition | `node50EntropyThreshold` | both | kernel-checked, conditional |
| N50-HIGH | The yes constructor is `threshold ≤ η(R)`. | `[49]` | `Node50High` | `[51]` | kernel-checked, conditional |
| N50-LOW | The no constructor is the strict complement `η(R) < threshold`. | ordered split | `Node50Low` | `[53]` | kernel-checked, conditional |
| N50-EXHAUSTIVE | High and low are mutually exhaustive for real numbers. | Core | `node50EntropyProfile.exhaustive`; `node50_exhaustive` | both | kernel-checked, conditional |
| N50-ROUTE | Core owns the bypass of node [20] and the handled rank-drop leaf, retains the exact node-[49] active value, and creates no other case. | framework | `ActiveCursorDecisionNoContinuationBypass`; `FocusedBranchDecision`; `decideActiveCursorDecisionNoContinuation` | both | kernel-checked, conditional |
| N50-WORK | The proof-level ordered comparison performs zero local finite scans. | Core | `node50ThresholdWork_eq_zero`; `node50LocalChecks = 0` | both | kernel-checked, conditional |

## Status

Partial with its local implementation kernel-checked; inherited missing
producers remain to be discharged.
Node [50] proves only the original two-way diamond. It does not produce node
[51]'s bit contribution, node [52]'s joint accounting, node [53]'s budget
comparison, or either node-[54] closure.
