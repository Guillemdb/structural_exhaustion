# Node [39] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[39]` |
| Incoming edge | `[38]` yes |
| Outgoing edge | terminal proper-atom compression contradiction |
| Local responsibility | Transport the retained representative along exact carrier equality and close it by the existing graph CT3/minimality theorem. |
| Framework operation | `State.StageNode.closeActiveCursorYesContinuationFinalYes`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N39-1 | Obtain the representative only on the literal at-original edge. | `[38]` equality + `[35]` certificate | `certificate.originalRepresentative` in `node39P13ProperAtomCompression` | terminal | kernel-checked, conditional |
| N39-2 | Execute stored CT3 compression and contradict minimality of the proper atom. | graph layer | `Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible` | terminal | kernel-checked, conditional |
| N39-3 | Close only the yes leaf and preserve the enlarged sibling. | framework | `Node39Stage` | terminal | kernel-checked, conditional |

## Status

Node [39] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. No global rank-drop closure is assigned to node [39].
