# Node [15] repair template

| Field | Value |
|---|---|
| Incoming edges | [14] -> [15] |
| Outgoing edges | yes -> [16]; no -> [17] |
| Local responsibility | Exhaustively decide whether the selected graph is P13-free. |
| Retained facts | Literal node-[14] hereditary-uncompressibility stage and the one full accumulated ledger. |
| New output | Framework-owned yes/no P13-free decision stages. |
| CT chain | `StageNode.decideUsingStage` on the immediate node-[14] stage. |
| Immediate consumers | [16], [17] |

## Obligations

| Task ID | Assertion | Producer | Evidence | Edge | Status |
|---|---|---|---|---|---|
| N15-PRED | Consume only the literal `Node14Stage`; recover its selected context through the typed predecessor | [14], framework | `Node15Input`, `Node15Context` | [14]->[15] | proved; kernel checked |
| N15-DECIDE | Exhaustively decide P13-free | [15] | `node15P13Decision`, `node15_exhaustive` | both | proved |
| N15-YES | Preserve exact free certificate | [15] | `DependentDecision.yesBranch` | yes->[16] | proved |
| N15-NO | Preserve the exact not-free certificate on the same node-[14] predecessor | [15] | `DependentDecision.noBranch` | no->[17] | proved |
| N15-CERT | Let the framework retrieve, split, and retain the immediate predecessor | framework | `StageNode.decideUsingStage` | both | proved; kernel checked |

Forbidden: a separate node-[4] query, application-owned dichotomy, or sibling-branch assumptions.
