# Node [13] repair template

| Field | Value |
|---|---|
| Incoming edges | [12] -> [13] |
| Outgoing edges | [13] -> [14] |
| Local responsibility | Prove the paper's replacement lemma for the target-complete atom/context interface. |
| Retained facts | Literal node-[12] universality stage and inherited atom/profile data. |
| New output | Replacement certificate only. |
| CT chain | CT2/CT3 replacement successor owned by the framework. |
| Immediate consumers | [14] |

## Obligations

| Task ID | Assertion | Producer | Evidence | Edge | Status |
|---|---|---|---|---|---|
| N13-PRED | Consume literal Node12Stage | [12] | `node13Replacement` via `StageNode.mapStage` | [12]->[13] | proved |
| N13-REPLACE | Exclude an exact one-way obstruction-preserving replacement | [13] | `Node13Output`; graph-owned `Compression.impossible` | [13]->[14] | proved |
| N13-SEM | Retain certified CT3 semantics, terminal, trace, totality, and work | CT3 graph producer | `Compression.run`, `run_terminal`, `run_trace`, `run_total`, `run_polynomial` | [13]->[14] | proved |
| N13-LEDGER | Append replacement fact once | framework | `Node13Stage`; `StageNode.mapStage` | downstream | proved |

Focused one-job kernel build passed through node [14].

Forbidden: predecessor copies, manual route, or all-boundaries bundling.
