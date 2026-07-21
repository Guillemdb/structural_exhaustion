# Node [38] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[38]` |
| Incoming edge | `[36]` yes |
| Outgoing edges | yes → `[39]`; no → `[40]` |
| Local responsibility | Decide whether the context-universal certificate's carrier is the original proper atom or a strict enlargement. |
| Retained facts | Node-[35] certificate and node-[36] universal response theorem. |
| New output | Exact carrier equality, or exact strict support growth. |
| Framework operation | `State.StageNode.decideActiveCursorYesContinuationYes` using `certificate.location`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N38-1 | At-original means the stored representative transports to the proper atom. | `[35]` certificate | `Node38AtOriginal`; `certificate.originalRepresentative` is consumed only at `[39]` | yes | kernel-checked, conditional |
| N38-2 | The complementary case is connected strict enlargement `C ⊊ Z`. | `[35]` inclusion and router | `Node38Enlarged` | no | kernel-checked, conditional |
| N38-3 | Execute the exact exhaustive location split. | `[36]` yes | `node38AtOriginalDecidable`, `node38EnlargedOfNotAtOriginal` | both | kernel-checked, conditional |
| N38-4 | Consume node [36] directly; node [37] is only an independently accumulated sibling terminal. | framework | `node38P13ProperRepresentativeDecision` requires `Node36Stage` | both | kernel-checked, conditional |

## Status

Node [38] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. Node [38] performs neither compression nor support-scope
classification.
