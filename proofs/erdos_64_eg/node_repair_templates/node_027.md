# Node [27] repair template

| Field | Value |
|---|---|
| Incoming | [26] -> [27] |
| Outgoing | [27] -> [28] |
| Responsibility | Prove that no component of Residual A has an internal 3-core. |
| Retained facts | Inherited through the accumulated ledger: node26 remainder, componentwise P13-freeness, minimality, and the target theorem input. |
| New output | The componentwise no-internal-3-core certificate only. |
| CT chain | Framework residual successor using the graph criticality profile. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N27-PRED | Consume literal Node26Stage | [26] | `node27P13NoInternalThreeCore` | kernel-checked, conditional |
| N27-NO3CORE | Exclude an internal minimum-degree-three core in each component | [27] | `Node27Output.noInternalThreeCore`; `Node27Output.noInternalSubgraphThreeCore` | kernel-checked, conditional |
| N27-LEDGER | Append the certificate without rebuilding Residual A | framework | `State.StageNode.mapDependentDecisionOnNoYesClosedActive` | kernel-checked, conditional |

Forbidden: defining a new remainder, re-running the packing, or proving node28 deficiency facts.

Node [27] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger and
`Node23DenseWindowQuietBlockInput`. Its thin output contains only the
node-[27] no-three-core certificate; it does not copy its predecessor. The
node-local producer showed no `sorryAx`.
