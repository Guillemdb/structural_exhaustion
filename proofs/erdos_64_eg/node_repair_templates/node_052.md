# Node [52] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[52]` |
| Incoming edge | `[51] -> [52]` on node [50]'s yes branch |
| Outgoing edge | `[52] -> [54]` |
| Local responsibility | Combine the already established same-context window and remainder bit contributions with the inherited near-cubic skeleton capacity, retain the exact joint feasibility inequality, and derive the high-entropy density cap. |
| Retained branch facts | The literal node-[50] active/high data, literal node-[51] remainder-bit output, node-[24] high-entropy transformer, and the complete accumulated ledger. |
| New output | `Node24HighEntropyJointBudget` and its exact `Node24HighEntropyCap` consequence on that same node-[51] leaf. |
| CT/framework chain | Core `LedgerQuery.entailedStage` plus `StageNode.mapFocusedBranchYesContinuationDerived`. |
| Immediate consumer | Node `[54]` only. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N52-PROV | Consume the literal node-[51] output on node [50]'s high constructor. | `[51]` | `Node52Stage`; `mapFocusedBranchYesContinuationDerived` | `[54]` | kernel-checked, conditional |
| N52-WINDOW | Retrieve node [24]'s density transformer from the one accumulated ledger; do not reopen or recompute its packing support. | `[24]` | `node52InheritedQuery`; `Node24HighEntropyTransformer` | `[54]` | kernel-checked, conditional |
| N52-JOINT | Add the window and node-[51] remainder contributions in the same near-cubic skeleton budget. | `[21]`, `[24]`, `[51]` | `Node52JointAccountingCertificate.jointBudget` | `[54]` | missing producer; local conditional adapter proved |
| N52-CAP | Derive the fixed-point high-entropy bound on the packing density from the exact joint budget. | `[24]` transformer, N52-JOINT | `Node52Output.thetaBound` | `[54]` | kernel-checked, conditional |
| N52-TOPOLOGY | Introduce no decision or residual branch at node [52]. | immutable Part-IV diagram | one `FocusedBranchDecisionYesContinuation`; no application sum | `[54]` | kernel-checked, conditional |
| N52-ROUTE | Preserve the bypass and node-[50] low leaf literally while replacing only the exact node-[51] payload. | Core | `mapFocusedBranchYesContinuationDerived` | `[54]` | kernel-checked, conditional |
| N52-WORK | Perform no graph, graph-family, Boolean-state, support, or completion-universe scan. | symbolic accounting | `node52LocalChecks = 0` | `[54]` | kernel-checked, conditional |

## Status

Partial with the local adapter kernel-checked. The missing joint-accounting producer is narrowly indexed by the
exact residual, node-[50] active/high leaf, and node-[51] value, and is the
only remaining local mathematical producer.  It preserves the old output
during migration but is not unconditional evidence.  The former
application-owned independent/dependent split is not part of the repaired
node and is not an edge in the original diagram.
