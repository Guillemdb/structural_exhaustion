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
| N54-52-PROV | Consume the literal node-[52] output on node [50]'s high constructor. | `[52]` | `Node54HighTerminal`; framework terminal bypass | terminal | kernel-checked |
| N54-52-STRICT | Identify high theta as the strict reverse of node [52]'s exact finite joint budget. | `[52]` | `Node54HighTheta` | terminal | kernel-checked |
| N54-52-CLOSE | Derive `not highTheta` by `A <= B -> not (B < A)`. | `[52]` | `node54HighTerminal` | terminal | kernel-checked |
| N54-53-PROV | Consume only node [53]'s literal strict-small constructor. | `[53]` | no public shortcut accepted; must be implemented through the eventual `Node54Stage` terminalizer | terminal | missing |
| N54-53-CAPACITY | Retrieve the certified powered table product on the identical realized-state carrier. | missing producer on the full-rank path | no unconditional ledger producer yet | terminal | missing |
| N54-53-CLOSE | Raise the product inequality to power ten, use the strict node-[50] bound, and contradict node [53]. | N54-53-CAPACITY, `[53]` | no public shortcut accepted; must retrieve the capacity fact from the ledger | terminal | missing |
| N54-ROUTE | Preserve earlier bypasses, retain node-[52] terminal evidence, eliminate only node-[53] small, and expose only node-[53] large. | framework | not yet declared as `Node54Stage` | `[55]` | missing |
| N54-WORK | Perform no local finite scan. | order arithmetic | `node54HighLocalChecks = 0` | terminal | kernel-checked |

## Status

Yellow. The `[52] -> [54]` incoming edge is kernel-checked. The `[53] --yes--> [54]`
edge is not exposed as a public conditional theorem: node [54] may consume only
the literal previous framework stage and facts retrieved from the single
accumulated ledger. The missing item is the earlier full-rank-path producer of
the powered table-product fact. Until that producer exists in the ledger, the
complete `Node54Stage` terminalizer is not declared, and node [55] cannot be
treated as receiving an unconditional large residual from node [54].
