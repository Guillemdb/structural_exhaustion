# Node [6] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [6] |
| Incoming edges | [5] -> [6] |
| Outgoing edges | yes -> [7]; no -> [8] |
| Local responsibility | Exhaustively decide whether a Mersenne return exists. |
| Retained branch facts | Minimal counterexample and node-[5] target algebra. |
| New output | Exact CT1 target/avoidance branch stages. |
| CT chain | One framework-owned CT1 dependent execution. |
| Immediate consumers | [7], [8] |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N6-PRED | Consume literal node-[5] stage | [5] | `node6MersenneDecision` requires `Available Node5Stage` | [5]->[6] | proved |
| N6-QUERY | Retrieve target algebra and current object from the ledger | [4],[5] | `executeCertificateUsingStage` retrieves the literal `Node5Stage`; `node6Input` uses its retained node-[4] context | [5]->[6] | proved |
| N6-RUN | Execute one exhaustive CT1 decision | [6] | `CT1.ResidualRefinement.executeCertificateUsingStage`; `node6MersenneDecision` | both | proved |
| N6-YES | Preserve the exact Mersenne-return witness | [6] | `CT1.ResidualRefinement.CertificateDecision.c1` | yes->[7] | proved |
| N6-NO | Preserve exact target avoidance | [6] | `CT1.ResidualRefinement.CertificateDecision.avoiding` | no->[8] | proved |
| N6-CERT | Retain trace, semantics, totality, and work evidence | CT1 | `node6_semantics`, `node6_trace_exact`, `node6_total`, `node6_work_bound` | both | proved |

## Framework and validation record

- Separate caller-selected yes/no CT1 runs are not node [6].
- No application-owned decision or route type is permitted.
- Focused kernel commands: `lake build StructuralExhaustion.CT1.ResidualRefinement` and `lake build Erdos64EG.Node6MersenneDecision`.
- Dashboard/TeX synchronization: pending.
