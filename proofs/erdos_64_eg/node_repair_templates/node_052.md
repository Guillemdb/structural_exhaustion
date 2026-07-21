# Node [52] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[52]` |
| Incoming edge | `[51] -> [52]` on node [50]'s yes branch |
| Outgoing edge | `[52] -> [54]` |
| Local responsibility | Combine the realized remainder states and dependent hot-window choices in one skeleton capacity, normalize the exact powered inequality, and add node [51]'s remainder-bit lower bound. |
| Retained branch facts | Literal node-[50] active/high data, literal node-[51] remainder-bit output, canonical accumulated hot aggregate, and the complete residual ledger. |
| New output | Exact joint, skeleton, powered, logarithmic, and final joint-budget inequalities on the same node-[51] leaf. |
| CT/framework chain | `DependentOwnerGlueCapacity`, `PoweredJointNormalization`, and `State.StageNode.mapFocusedBranchYesContinuation`. |
| Immediate consumer | Node `[54]` only. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N52-PROV | Consume the literal node-[51] output on node [50]'s high constructor. | `[51]` | `Node52Stage`; `mapFocusedBranchYesContinuation` | `[54]` | kernel-checked |
| N52-JOINT | Count only remainder states and hot-window choices realized by the same compatible completion, and inject them into one skeleton code. | `[49]` | `Node52JointCapacity`; `node49_realizedRemainder_mul_hotChoices_le_skeletonCode` | `[54]` | kernel-checked |
| N52-SKELETON | Bound that joint code by the inherited labelled baseline-skeleton capacity. | accumulated aggregate | `Node52SkeletonCapacity` | `[54]` | kernel-checked |
| N52-NORMALIZE | Raise the exact capacity inequality to the certificate exponent and retain hot-scale loss and cold-window mass explicitly as error. | `[21]`, N52-JOINT | `node52NormalizationProfile`; `Node52NormalizedJointCapacity` | `[54]` | kernel-checked |
| N52-LOG | Apply the framework logarithmic transport without enumerating a state product. | N52-NORMALIZE | `Node52LogarithmicJointCapacity`; `PoweredJointNormalization.Profile.logb_withError` | `[54]` | kernel-checked |
| N52-BUDGET | Add node [51]'s inherited remainder-bit lower bound to the logarithmic window inequality. | `[51]`, N52-LOG | `Node52JointBudget`; `Node52Output.jointBudget` | `[54]` | kernel-checked |
| N52-TOPOLOGY | Introduce no decision or residual branch at node [52]. | immutable Part-IV diagram | one `FocusedBranchDecisionYesContinuation`; no application sum | `[54]` | kernel-checked |
| N52-ROUTE | Preserve the bypass and node-[50] low leaf literally while replacing only the exact node-[51] payload. | Core | `mapFocusedBranchYesContinuation` | `[54]` | kernel-checked |
| N52-WORK | Perform no graph, graph-family, Boolean-state, support, or completion-universe scan. | symbolic accounting | `node52LocalChecks = 0` | `[54]` | kernel-checked |

## Status

All node-[52] obligations are kernel-checked on the exact incoming residual.
The framework owns the continuation and joint-capacity plumbing; node [52]
introduces no additional branch or caller-supplied certificate.
