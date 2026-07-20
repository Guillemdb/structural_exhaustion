# Node [60] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[60]` |
| Incoming edge | `[59] --yes--> [60]` |
| Outgoing edge | branch-local terminal; node-[59] no survives toward `[61]` |
| Local responsibility | Contradict nonnegative global net charge with the retained node-[57] strict-quarter cap and node-[58] defining equality. |
| Retained facts | Exact node-[57] strict-quarter output, exact node-[58] charge, node-[59] nonnegative proof, complete accumulated ledger, and bypasses. |
| New output | Branch-local `False` on the node-[59] yes constructor. |
| CT/framework chain | `State.StageNode.closeFocusedBranchYes`; `FocusedBranchDecisionYesClosed` exposes only the original no leaf. |
| Immediate consumer | Node `[61]` receives the literal strict-negative node-[59] leaf. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N60-PROV | Consume only the literal node-[59] nonnegative constructor. | `[59]` | `Node60Stage`; `node60P13NetCapContradiction` | terminal | source-authored, pending kernel check; conditional |
| N60-CAP | Retrieve node [57]'s exact `4(def+-sigma_R)<|R|` from the same framework active carrier. | `[57]` | `active.data.output.strictQuarter` in `node60P13NetCapImpossible` | terminal | source-authored, pending kernel check; conditional |
| N60-CHARGE | Rewrite node [59]'s sign using node [58]'s exact definition of `N(R)`. | `[58]`, `[59]` | `active.output.netChargeExact` | terminal | source-authored, pending kernel check; conditional |
| N60-CLOSE | Derive the local contradiction `0 <= N(R) < 0`. | N60-CAP, N60-CHARGE | `node60P13NetCapImpossible` | terminal | source-authored, pending kernel check; conditional |
| N60-ROUTE | Eliminate only yes, preserve every bypass, and expose the literal strict-negative no leaf for node [61]. | framework | `FocusedBranchDecisionYesClosed`; `closeFocusedBranchYes` | `[61]` | source-authored, pending kernel check; conditional |
| N60-WORK | Perform only symbolic cast and linear arithmetic. | local real arithmetic | `node60LocalChecks = 0` | terminal | source-authored, pending kernel check; conditional |

## Status

Yellow only because its dependency cone includes the exact node-[57]
missing producer.  The branch-local contradiction uses no new
assumption at node [60], closes no sibling branch, and awaits the root agent's
serialized focused Lean check.
