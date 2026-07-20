# Node [56] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[56]` |
| Incoming edge | `[55]` |
| Outgoing edge | Residual C continuation to Part V node `[57]` |
| Local responsibility | Combine the inherited window-density and surplus-adjusted supply facts into the finite error-bearing net-deficiency cap, and prove the limiting constant is below `1/4`. |
| Retained facts | Literal node-[55] leaf; node-[24] packing density; node-[25] remainder normalization; node-[29] incidence/surplus supply; complete accumulated ledger. |
| New output | `netDef <= tau_win |R| + E_56` and `tau_win < 1/4`. |
| CT/framework chain | `State.StageNode.continueFocusedBranchActive`; the finite net-cap producer remains missing on the exact leaf. |
| Immediate consumer | Node `[57]`. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N56-PROV | Consume only the literal Residual C leaf from node [55]. | `[55]` | `Node56Stage`; `node56P13NetDeficiencyCap` | `[57]` | kernel-checked, conditional |
| N56-NUMERATOR | Use exactly positive deficiency minus remainder surplus. | `[29]` | `node56NetDeficiencyNumerator` | `[57]` | kernel-checked, conditional |
| N56-CONSTANT | Define `tau_win = 15 theta_win / (1 - 13 theta_win)` in exact rational form. | `[24]` | `node56TauWindow` | `[57]` | kernel-checked, conditional |
| N56-FINITE | Derive the exact finite error-bearing cap from node [24]'s density and node [29]'s surplus-adjusted supply. | `[24]`, `[25]`, `[29]` | `Node56Output.netCap` | `[57]` | missing same-ledger producer |
| N56-QUARTER | Prove the exact limiting constant is strictly below `1/4`. | fixed arithmetic | `node56TauWindow_lt_quarter`; `Node56Output.limitingCapStrict` | `[57]` | kernel-checked, conditional |
| N56-ERROR | Retain the finite total-surplus error explicitly; its previously verified near-cubic `o(|R|)` transport remains legacy support until migrated to this active carrier. | `[19]`, `[29]` | `node56NetError`; preserved `P13Node56Refinement` asymptotic theorem | `[57]` | partial; exact finite payload retained |
| N56-ROUTE | Append only node [56]'s payload; Core keeps the exact node-[55] active data and every terminal bypass. | framework | `FocusedBranchActiveContinuation`; `continueFocusedBranchActive` | `[57]` | kernel-checked, conditional |
| N56-WORK | Perform no graph, support, context, or state-family scan. | symbolic arithmetic | `node56LocalChecks = 0` | `[57]` | kernel-checked, conditional |

## Status

Yellow with the local adapter and exact constant arithmetic kernel-checked.
The exact old finite net cap is reused only through
the missing net-cap producer, indexed by the literal node-[55] leaf. The
remaining optimization is to expose the already proved node-[24]/[25]/[29]
inputs through same-ledger queries and port the old asymptotic error theorem;
neither task changes a diagram node or edge.
