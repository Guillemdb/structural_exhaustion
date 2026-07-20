# Node [41] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[41]` |
| Incoming edge | `[40]` |
| Outgoing edges | yes `[42]`; no `[43]` |
| Local responsibility | Decide whether the exact enlarged connected carrier `Z` is a proper support or the whole graph. |
| Retained facts | Node-[35] admitted CT15 circuit and support certificate; node-[36] original-interface universality; node-[38] strict enlargement `C ⊊ Z`; all earlier ledger facts. |
| New output | The exhaustive proper/whole branch proof for that same carrier. |
| Framework operation | `State.StageNode.decideFocusedBranch` on node [40]'s focused active leaf. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N41-CARRIER | The classified carrier is the same `Z` selected by the node-[35] determination certificate. | `[35]`, retained by `[40]` | `Node41Active`; `Node35CollisionSupportCertificate.carrierExact` | both | kernel-checked, conditional |
| N41-PROPER | The yes constructor is exactly `Z ⊊ G`. | graph support interface | `Node41Proper` / `Interface.OriginalEligible` | `[42]` | kernel-checked, conditional |
| N41-WHOLE | The no constructor is exactly `Z = G`. | graph support interface | `Node41Whole` / `Interface.IsWhole` | `[43]` | kernel-checked, conditional |
| N41-EXHAUSTIVE | Proper versus whole is exhaustive and disjoint because it reads the stored `Scope` tag. | graph layer | `Interface.originalEligibleDecidable`; `Interface.whole_of_not_originalEligible` | both | kernel-checked, conditional |
| N41-ROUTE | Preserve every unrelated terminal leaf and the exact node-[40] payload. | framework | `node41P13CarrierScopeDecision`; `FocusedBranchDecision` | both | kernel-checked, conditional |
| N41-WORK | Inspect no graph, support family, quotient family, or context family. | framework/graph tag | `node41LocalChecks = 0` | both | kernel-checked, conditional |
| N41-RUN | Append the decision to the one accumulated residual ledger. | `[40]` runner | `runInitialThroughNode41` | both | kernel-checked, conditional |

## Status

Node [41] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. Node [41] proves no proper-support closure, repair identity, or
whole-graph barrier.
