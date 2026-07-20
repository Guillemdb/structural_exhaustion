# Node [51] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[51]` |
| Incoming edge | `[50] --yes--> [51]` |
| Outgoing edge | `[51] -> [52]` |
| Local responsibility | On the exact high-entropy constructor, use node [49]'s constrained-family entropy identity to prove that the remainder contributes at least `(|R|/10) log_2 n` bits. |
| Retained branch facts | The literal full-rank node-[49] active leaf, node [50]'s high proof, and the complete accumulated ledger. |
| New output | The single real inequality `(|R|/10) log_2 n <= log_2 |G(R)|`. |
| CT/framework chain | `OrderThresholdSplit` at node [50], followed by Core `StageNode.continueFocusedBranchYes`. |
| Immediate consumer | Node `[52]` only. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N51-PROV | Consume the literal yes constructor of node [50], not a restated entropy inequality. | `[50]` | `Node51Stage`; `node51P13HighEntropyBranch` | `[52]` | kernel-checked, conditional |
| N51-IDENTITY | Use the exact constrained-family identity for `eta(R)` without reconstructing or enumerating `G(R)`. | `[49]` | `active.output.entropyExact` in `node51Output` | `[52]` | kernel-checked, conditional |
| N51-SCALE | Multiply the high threshold by the nonnegative remainder size, treating the zero-remainder case soundly. | `[50]` high proof | `node51Output` (`cardRNonnegative`, zero/nonzero split) | `[52]` | kernel-checked, conditional |
| N51-BITS | Obtain `(|R|/10) log_2 n <= log_2 |G(R)|`. | `[49]`, `[50]` | `Node51Output.remainderBits` | `[52]` | kernel-checked, conditional |
| N51-SCOPE | Do not assert joint window--remainder feasibility or a density cap. | diagram/prose | `Node51Output` has only `remainderBits` | `[52]` | kernel-checked, conditional |
| N51-ROUTE | Preserve the framework bypass and the node-[50] low leaf literally. | Core | `FocusedBranchDecisionYesContinuation`; `continueFocusedBranchYes` | `[52]` | kernel-checked, conditional |
| N51-WORK | Perform no graph, family, support, or context scan. | symbolic arithmetic | `node51LocalChecks = 0` | `[52]` | kernel-checked, conditional |

## Status

Yellow with its local implementation kernel-checked, pending discharge of
inherited missing obligations. Node [51] itself introduces no new assumption and no branch,
edge, completion universe, or finite-family enumeration.
