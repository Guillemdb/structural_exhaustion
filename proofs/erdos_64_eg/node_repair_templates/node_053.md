# Node [53] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[53]` |
| Incoming edge | `[50] --no--> [53]` |
| Outgoing edges | yes `[54]`; no `[55]` |
| Local responsibility | Decide whether the remaining non-curvature labelled-skeleton budget is strictly smaller than the forced curvature cost. |
| Retained facts | Literal node-[50] active/low data, node-[52] high output on its sibling, and the complete accumulated ledger. |
| New output | The exhaustive strict-small/complementary-large ordered comparison. |
| CT/framework chain | `State.StageNode.decideFocusedBranchYesContinuationNo`. |
| Immediate consumers | Node `[54]` on yes; node `[55]` on no. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N53-PROV | Consume only node [50]'s literal low constructor after node [52] has independently advanced the high constructor. | `[50]`, `[52]` | `Node53Stage`; `node53P13RemainingBudgetDecision` | both | kernel-checked, conditional |
| N53-SKELETON | Use the exact labelled baseline-skeleton bit capacity on the fixed graph order. | earlier skeleton ledger | `node53SkeletonBits` | both | kernel-checked, conditional |
| N53-WINDOW | Use the already normalized window demand; do not enumerate window states. | `[22]` | `node53WindowBits` | both | kernel-checked, conditional |
| N53-REMAINDER | Use node [49]'s exact symbolic constrained-family count. | `[49]` | `node53RemainderBits` | both | kernel-checked, conditional |
| N53-FORCED | Name the forced full-rank curvature cost already established at nodes [47]--[48]. | `[47]`, `[48]` | `node53ForcedCurvatureBits` | both | kernel-checked, conditional |
| N53-SMALL | The yes constructor is `remaining < forced`. | local comparison | `Node53Small` | `[54]` | kernel-checked, conditional |
| N53-LARGE | The no constructor is the exact ordered complement `forced <= remaining`. | Core ordered complement | `Node53Large` | `[55]` | kernel-checked, conditional |
| N53-ROUTE | Retain node [52]'s high output and every bypass; create no extra case. | framework | `FocusedBranchYesContinuationNoDecision` | both | kernel-checked, conditional |
| N53-WORK | Perform no finite graph, family, support, or context scan. | symbolic scalar decision | `node53LocalChecks = 0` | both | kernel-checked, conditional |

## Status

Yellow with its local implementation kernel-checked, pending discharge of
inherited missing obligations. Node [53] itself accepts no conclusion or branch assumption and proves
only the original diagram diamond.
