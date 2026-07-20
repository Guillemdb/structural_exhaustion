# Node [14] repair template

| Field | Value |
|---|---|
| Incoming edges | [13] -> [14] |
| Outgoing edges | [14] -> [15] |
| Local responsibility | Prove hereditary target-uncompressibility of proper supports. |
| Retained facts | Literal replacement stage and prior atom/context facts. |
| New output | Hereditary uncompressibility certificate only. |
| CT chain | CT3 proper-support successor through framework stage mapping. |
| Immediate consumers | [15] |

## Obligations

| Task ID | Assertion | Producer | Evidence | Edge | Status |
|---|---|---|---|---|---|
| N14-PRED | Consume literal Node13Stage | [13] | `node14Uncompressibility` via `StageNode.mapStage` | [13]->[14] | proved |
| N14-UNCOMP | Exclude target-complete compression by converting it to node-[13] replacement data | [14] | `Node14Output.noTargetCompleteCompression`; `Compression.ofTargetComplete`; `node13.output` | [14]->[15] | proved |
| N14-DEFECT | Show a non-universal identification is non-target-complete and carries a distinguishing context | [12],[14] | `Node14Output.defectiveIdentification`; node-[12] output; `targetDefective_of_not_contextEquivalent` | [14]->[15] | proved |
| N14-SCOPE | Restrict both clauses to proper atoms | [14] | `Node14Output` quantifies only `Node11ProperAtom` | [14]->[15] | proved |
| N14-LEDGER | Append only the new hereditary fact | framework | `Node14Stage`; `StageNode.mapStage` | downstream | proved |

Focused kernel command: `cd examples/erdos_64_eg && lake -Kjobs=1 build Erdos64EG.Node14Uncompressibility` (passed).

Forbidden: assigning node-[15] dichotomy or HSS closure to this node.
