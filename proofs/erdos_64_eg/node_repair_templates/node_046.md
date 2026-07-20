# Node [46] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[46]` |
| Incoming edge | `[45]` |
| Outgoing edge | branch-local terminal |
| Local responsibility | Close the remaining whole-support rank-drop leaf by combining node [45]'s quotient-code injectivity with node [35]'s retained distinct identified pair. |
| Retained facts | Exact node-[45] output, node-[35] CT15 pair circuit, and every earlier ledger fact. |
| New output | Contradiction on the live whole-support leaf only. |
| Framework operation | `State.StageNode.closeFocusedBranchNoContinuation`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N46-PROV | Consume the literal node-[45] whole-support payload. | `[45]` | `node46P13RankDropClosure` requires `Node45Stage` | terminal | kernel-checked, conditional |
| N46-COLLISION | Two distinct declared raw curvature coordinates have equal quotient code. | `[35]` | `PairCircuit.distinct`; `PairCircuit.identified` retained in `Node41Active` | terminal | kernel-checked, conditional |
| N46-INJECTIVE | The same quotient code is injective. | `[45]` | `Node45Output.exactRawLabels` | terminal | kernel-checked, conditional |
| N46-CLOSE | Injectivity of the identified pair contradicts its distinctness. | `[35]`, `[45]` | `node46WholeRankDropImpossible` | terminal | kernel-checked, conditional |
| N46-ROUTE | Eliminate only the live node-[45] leaf; retain all already handled Part-III siblings as terminal bypass data. | framework | `FocusedBranchDecisionNoClosed`; `closeFocusedBranchNoContinuation` | terminal | kernel-checked, conditional |
| N46-WORK | Perform no graph, quotient, support, or context scan. | proof-level | `node46LocalChecks = 0` | terminal | kernel-checked, conditional |
| N46-RUN | Append the terminal result to the one accumulated ledger. | `[45]` runner | `runInitialThroughNode46` | terminal | kernel-checked, conditional |

## Status

Yellow with its local implementation kernel-checked, pending discharge of the
inherited missing obligations at nodes [21], [23], and [35]. Node [46] imports
no full-rank Residual B fact and proves no Part-IV statement.
