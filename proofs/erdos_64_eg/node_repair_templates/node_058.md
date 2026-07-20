# Node [58] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[58]` |
| Incoming edge | `[57]` |
| Outgoing edge | `[59]` |
| Local responsibility | Define the exact net charge `N(R)=def+(R)-sigma(R)-|R|/4` on the large-budget residual. |
| Retained facts | Literal node-[57] strict-quarter output; Residual C branch indices; complete accumulated ledger and bypasses. |
| New output | One exact real-valued net charge and its defining equality. |
| CT/framework chain | `State.StageNode.continueFocusedBranchActiveAgain`; `FocusedBranchActiveData` retains node [57] inside Core. |
| Immediate consumer | Node `[59]`. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N58-PROV | Consume only the literal node-[57] active continuation. | `[57]` | `Node58Active`; `node58P13NetCharge` | `[59]` | source-authored, pending kernel check; conditional |
| N58-DEF | Define exactly `def+(R)-sigma_R-|R|/4`, using node [56]'s already fixed numerator. | `[56]`, `[57]` | `node58NetCharge` | `[59]` | source-authored, pending kernel check; conditional |
| N58-EXACT | Retain the exact defining equality, not a detached sign or global conclusion. | local definition | `Node58Output.netChargeExact` | `[59]` | source-authored, pending kernel check; conditional |
| N58-ROUTE | Core retains node [57] and appends only the node-[58] value on the active leaf; bypasses are unchanged. | framework | `FocusedBranchActiveData`; `continueFocusedBranchActiveAgain` | `[59]` | source-authored, pending kernel check; conditional |
| N58-SCOPE | Do not decide the sign or localize a component at node [58]. | paper topology | absence of a branch predicate in `Node58Output` | `[59]` | source-authored, pending review |
| N58-WORK | Perform no graph, component, context, or state-family scan. | exact definition | `node58LocalChecks = 0` | `[59]` | source-authored, pending kernel check; conditional |

## Status

Yellow through node [57]'s typed migration boundary.  Its paper-local net
charge definition and framework-only transport are source-complete and await
the root agent's serialized focused Lean check.
