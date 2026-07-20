# Node [17] repair template

| Field | Value |
|---|---|
| Incoming | [15] no -> [17] |
| Outgoing | [17] -> [18] |
| Responsibility | Retain the selected maximal vertex-disjoint induced-P13 packing, exposing no stronger cardinality claim. |
| Retained facts | Exact non-P13-free branch and full packed minimal-context ledger. |
| New output | Maximal induced-P13 packing only. |
| CT chain | Framework `CT12.DisjointPacking.Profile.MaximalVerifiedStage` successor on node-[15] no branch. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N17-PRED | Consume literal node15 no-stage after node16 closes yes | [15], [16] | `Node17Stage`, `runInitialThroughNode17` | proved; kernel checked |
| N17-PACK | Reuse the already verified proof-selected packing through a maximal-only graph/CT12 projection, with no maximum-cardinality field in the node output | [17], Graph, CT12 | `Graph.InducedPathMaximalPacking.verifiedStage`, `CT12.DisjointPacking.Profile.maximalVerifiedStage`, `node17InducedP13Packing`, `node17_maximal` | proved; kernel checked |
| N17-NONEMPTY | Use the retained node-[15] no proof to show the selected maximal packing is nonempty | [15], [17] | `node17_nonempty` | proved; kernel checked |
| N17-CERT | Retain disjointness, maximality, trace, totality, and selected-list work | CT12 | `Node17Output`, `node17_terminal`, `node17Total`, `node17WorkBudget` | proved; kernel checked |
| N17-LEDGER | Append packing once | framework | `StageNode.mapStage` | proved; kernel checked |

Forbidden: enumerating induced embeddings or packing families, exposing a maximum-cardinality field from the node output, manual Sigma/LedgerExtension, or node18 label algebra.
