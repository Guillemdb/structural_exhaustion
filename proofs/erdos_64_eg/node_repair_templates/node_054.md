# Node [54] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[54]` |
| Incoming edges | `[52]`; `[53] --yes--> [54]` |
| Outgoing edge | branch-local terminal; only node-[53] no survives toward `[55]` |
| Local responsibility | Exclude the strict reverse of node [52]'s joint cap and close node [53]'s strict small-budget leaf against its same-branch capacity certificate. |
| Retained facts | Exact node-[52] output; exact node-[53] small or large proof; every earlier accumulated fact. |
| New output | High-theta impossibility on the node-[52] terminal and contradiction on node-[53] small. |
| CT/framework chain | `State.StageNode.terminalizeFocusedBranchYesCloseNestedYes`. |
| Immediate consumer | Node `[55]` receives only the complementary large leaf. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N54-52-PROV | Consume the literal node-[52] output on node [50]'s high constructor. | `[52]` | `Node54HighOutput`; framework terminal bypass | terminal | kernel-checked, conditional |
| N54-52-STRICT | Identify high theta as the strict reverse of node [52]'s exact finite joint budget. | `[52]` | `Node54HighTheta` | terminal | kernel-checked, conditional |
| N54-52-CLOSE | Derive `not highTheta` by `A <= B -> not (B < A)`. | `[52]` | `node54HighOutput` | terminal | kernel-checked, conditional |
| N54-53-PROV | Consume only node [53]'s literal strict-small constructor. | `[53]` | `node54P13EntropyCapClosure` | terminal | kernel-checked, conditional |
| N54-53-CAPACITY | Prove the same-branch independent-capacity certificate from the accumulated rank/entropy ledger. | earlier rank/entropy ledger | node-[53] small-leaf capacity theorem | terminal | missing producer; local contradiction proved conditionally |
| N54-53-CLOSE | Contradict `remaining < forced` with `forced <= remaining`. | N54-53-CAPACITY, `[53]` | `node54SmallBudgetImpossible` | terminal | kernel-checked, conditional |
| N54-ROUTE | Preserve earlier bypasses, retain node-[52] terminal evidence, eliminate only node-[53] small, and expose only node-[53] large. | framework | `Node54Bypass`; `Node54Active`; `terminalizeFocusedBranchYesCloseNestedYes` | `[55]` | kernel-checked, conditional |
| N54-WORK | Perform no local finite scan. | order arithmetic | `node54LocalChecks = 0` | terminal | kernel-checked, conditional |

## Status

Yellow. The node-[52] terminal is kernel-checked conditionally. The node-[53] small closure
temporarily consumes one certificate indexed by the literal low/small leaf;
it cannot be used by the large-budget sibling and is not green evidence. The
entire local framework carrier and both consumers kernel-check.
