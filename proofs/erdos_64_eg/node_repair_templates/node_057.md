# Node [57] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[57]` |
| Incoming edge | Part-IV node `[56]` |
| Outgoing edge | `[58]` |
| Local responsibility | Specialize the inherited error-bearing large-budget net cap to the strict-quarter tail used by Part V. |
| Retained facts | Literal node-[56] active leaf; Residual C branch indices; complete accumulated ledger and every Part-IV terminal bypass. |
| New output | `4 (def+(R)-sigma_R) < |R|`. |
| CT/framework chain | `State.StageNode.mapFocusedBranchActiveContinuation`; the exact strict-quarter producer remains missing. |
| Immediate consumer | Node `[58]`. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N57-PROV | Consume only the literal node-[56] large-budget active leaf. | `[56]` | `Node57Stage`; `node57P13LargeBudgetNetCap` | `[58]` | source-authored, pending kernel check; conditional |
| N57-STRICT | Retain the exact denominator-free strict-quarter inequality on that same residual. | `[56]` asymptotic strict-quarter tail | `Node57Output.strictQuarter` | `[58]` | missing producer |
| N57-INDEX | Prevent the output from being consumed on a bypass or sibling branch. | `[55]`, `[56]` | theorem indexed by `Node55ResidualC` and literal `Node56Output` | `[58]` | missing kernel-checked producer |
| N57-ROUTE | Preserve every Part-IV bypass and replace only the active node-[56] payload. | framework | `mapFocusedBranchActiveContinuation` | `[58]` | source-authored, pending kernel check; conditional |
| N57-WORK | Perform no finite graph or state-family scan. | symbolic inequality transport | `node57LocalChecks = 0` | `[58]` | source-authored, pending kernel check; conditional |

## Status

Yellow.  The exact old strict-quarter result is isolated behind one
leaf-indexed missing obligation.  No axiom, admission, new case, or new diagram edge
is introduced.  The source awaits the root agent's serialized focused Lean
check.
