# Node [59] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[59]` |
| Incoming edge | `[58]` |
| Outgoing edges | yes `[60]`; no `[61]` |
| Local responsibility | Decide exactly whether the node-[58] global net charge is nonnegative. |
| Retained facts | Literal node-[57] strict-quarter output, literal node-[58] exact charge, Residual C indices, full accumulated ledger, and bypasses. |
| New output | Exhaustive ordered split `0 <= N(R)` or `N(R) < 0`. |
| CT/framework chain | `State.StageNode.decideFocusedBranchActiveContinuation`, returning the standard Core `FocusedBranchDecision`. |
| Immediate consumers | Node `[60]` on yes; node `[61]` on no. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N59-PROV | Decide the sign of the literal node-[58] charge on its exact active leaf. | `[58]` | `Node59Active`; `node59P13NetChargeDecision` | both | source-authored, pending kernel check; conditional |
| N59-YES | The yes constructor is exactly `0 <= N(R)`. | `[58]` | `Node59Nonnegative` | `[60]` | source-authored, pending kernel check; conditional |
| N59-NO | The no constructor is exactly the strict complement `N(R) < 0`. | ordered real comparison | `Node59Negative`; `lt_of_not_ge` | `[61]` | source-authored, pending kernel check; conditional |
| N59-EXHAUSTIVE | Construct both and only the paper's two sign outcomes. | Core ordered decision | `decideFocusedBranchActiveContinuation` | both | source-authored, pending kernel check; conditional |
| N59-ROUTE | Retain node-[57]/[58] data inside Core and preserve all earlier bypasses without an application-owned sum. | framework | `FocusedBranchActiveData`; `FocusedBranchDecision` | both | source-authored, pending kernel check; conditional |
| N59-WORK | Perform one proof-level comparison and no finite scan. | linear order on `Real` | `node59LocalChecks = 0` | both | source-authored, pending kernel check; conditional |

## Status

Yellow through the exact node-[57] typed migration boundary.  The two-way
paper diamond is source-authored with no extra constructor or edge and awaits
the root agent's serialized focused Lean check.
