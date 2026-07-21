# Node [31] repair template

| Field | Value |
|---|---|
| Incoming | [30] -> [31] |
| Outgoing | [31] -> [32] |
| Responsibility | Define the curvature target-rank of the retained remainder. |
| Retained facts | Inherited through the accumulated ledger: node30 remainder/wedge facts and the earlier target-response algebra. |
| New output | The exact CT15 curvature-rank state, without deciding rank drop. |
| CT chain | CT15 target-relative rank initialization. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N31-PRED | Consume literal Node30Stage | [30] | `node31P13CurvatureTargetRank`; `Node31Output.node30` | kernel-checked, conditional |
| N31-RANK | Instantiate the CT15 support-stratified functional-rank profile on Residual A | [31] | `p13CurvatureFunctionalRankProfile`; `p13CurvatureTargetRank`; `Node31Output.coordinateCount`; `Node31Facts.targetRankBound`; `Node31Facts.maximalSurvivingCoordinates` | kernel-checked, conditional |
| N31-SEM | Attach the exact coordinate response semantics and keep the induced raw proposal audit distinct | CT15/[31] | `Node31Facts.responseExact`; `p13CurvatureProposedFunctionalRankProfile` is reserved for the restricted proposal tested downstream | kernel-checked, conditional |
| N31-LEDGER | Append the rank state without deciding node32 | framework | generic active-cursor map | kernel-checked, conditional |

Node [31] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. Its thin output contains only the new CT15
rank facts; it does not copy node [30]. The node-local producer showed no
`sorryAx`.
The framework separates the support-stratified quotient rank used here from the raw
proposal induced on the original atom after circuit extraction.  Node [36]
audits that restricted raw proposal; no consumer may invoke the later global
full-rank theorem to erase Branch D before nodes [35]--[46] run.

Forbidden: rank-drop branching, a manual quotient handoff, or recomputing the remainder.
