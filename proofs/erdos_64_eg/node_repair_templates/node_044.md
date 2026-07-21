# Node [44] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[44]` |
| Incoming edge | `[43]` |
| Outgoing edge | `[45]` |
| Local responsibility | Prove the exact `1`--`3` repair-component identity `s = p - 2 + 2β - σ`. |
| Retained facts | Exact whole determination carrier and all earlier graph constraints. |
| New output | The symbolic identity for every finite component satisfying the paper's `1`--`3` component hypotheses. |
| Framework operation | `State.StageNode.mapFocusedBranchNoContinuation`; graph mathematics is `Graph.OneThreeRepair.Component.identity`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N44-PROV | Consume the exact node-[43] whole-support continuation. | `[43]` | `node44P13RepairIdentity` requires `Node43Stage` | `[45]` | kernel-checked, conditional |
| N44-FINITE | All counts belong to one supplied finite connected repair component. | graph component input | `Graph.OneThreeRepair.Component` | `[45]` | kernel-checked, conditional |
| N44-HANDSHAKE | `3s + σ + p = 2(e+p)` for that component. | graph layer | `Component.handshake`; `Component.internalEdgeCount_add_boundary` | `[45]` | kernel-checked, conditional |
| N44-CYCLERANK | `β = e - s + 1` for the same component. | graph layer | `Component.cycleRank_cast`; `Component.vertexCard_eq` | `[45]` | kernel-checked, conditional |
| N44-IDENTITY | Eliminate `e` to obtain `s = p - 2 + 2β - σ` over `Int`. | graph layer | `Node44Output.repairIdentity`; `Component.identity` | `[45]` | kernel-checked, conditional |
| N44-ROUTE | Replace only node [43]'s latest whole-branch payload; preserve every other leaf and the full ledger. | framework | `mapFocusedBranchNoContinuation` | `[45]` | kernel-checked, conditional |
| N44-WORK | Use symbolic degree-sum arithmetic; enumerate no components or graphs. | graph theorem | `node44LocalChecks = 0` | `[45]` | kernel-checked, conditional |

## Status

Node [44] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. Node [44] is the conditional arithmetic lemma stated by the paper;
it does not prove node [45]'s global barrier or node [46]'s contradiction.
