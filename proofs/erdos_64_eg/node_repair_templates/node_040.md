# Node [40] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[40]` |
| Incoming edge | `[38]` no |
| Outgoing edge | `[41]` |
| Local responsibility | Retain the same inclusion-minimal connected determination certificate on its strict enlarged carrier `Z ⊋ C`. |
| Retained facts | Node-[35] certificate, node-[36] universality, node-[38] strict growth. |
| New output | The active enlarged-support cursor; no duplicated application payload. |
| Framework operation | `State.StageNode.focusActiveCursorYesContinuationFinalNo`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N40-1 | `C ⊊ Z`. | `[38]` no proof | active-no constructor of `Node40Stage` | `[41]` | kernel-checked, conditional |
| N40-2 | `Z` is connected and carries/determines the same coordinates. | `[35]` certificate | certificate retained literally in `Node40Stage` | `[41]` | kernel-checked, conditional |
| N40-3 | The determination remains inclusion-minimal. | `[35]` certificate | retained `certificate.minimal` | `[41]` | kernel-checked, conditional |
| N40-4 | Consume node [38] directly; node [39] is an independently accumulated sibling closure. | framework | `node40P13EnlargedConnectedSupport` requires `Node38Stage` | `[41]` | kernel-checked, conditional |
| N40-5 | Do not decide whether `Z` is proper or whole. | `[41]` responsibility | no scope decision in this module | `[41]` | kernel-checked, conditional |

## Status

Node [40] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. The legacy `VerifiedP13Node40EnlargedSupport`/`ExactHandoff`
transport is not used; the single accumulated framework stage already retains
every field.
