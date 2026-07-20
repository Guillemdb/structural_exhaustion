# Node [36] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[36]` |
| Incoming edge | `[35]` |
| Outgoing edges | no → `[37]`; yes → `[38]` |
| Local responsibility | Audit the retained determination at the original atom interface against every outside context. |
| Retained facts | Node-[35] pair circuit and its exact support-stratified certificate. |
| New output | Either universal response equality at the original interface or one concrete response mismatch there. |
| Framework operation | `State.StageNode.decideActiveCursorYesContinuation` applied to `certificate.auditOriginal`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N36-1 | Use the original support's context type, not the final carrier's context type. | `[35]` certificate | `Node36OriginalUniversal`, `Node36OriginalDefect` | both | kernel-checked, conditional |
| N36-2 | Execute the exhaustive context audit without enumerating contexts. | `[35]` certificate | `node36OriginalUniversalDecidable`, `node36OriginalDefectOfNotUniversal` | both | kernel-checked, conditional |
| N36-3 | Preserve the outer bypass, full-rank sibling, and complete ledger. | framework | `node36P13OriginalContextAudit` | both | kernel-checked, conditional |
| N36-4 | Record zero local finite checks. | framework proof-level audit | `node36LocalChecks_eq_zero` | both | kernel-checked, conditional |

## Status

Node [36] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`; no focused-validation task remains.
