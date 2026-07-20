# Node [37] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[37]` |
| Incoming edge | `[36]` no |
| Outgoing edge | terminal target-defective quotient |
| Local responsibility | Expose and mark terminal the concrete original-context response mismatch already returned by node [36]. |
| New output | No additional mathematics; the literal no proof is the terminal certificate. |
| Framework operation | `State.StageNode.markActiveCursorYesContinuationNoTerminal`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N37-1 | Retain one original-interface context and exact mismatch. | `[36]` no proof | `Node37TargetDefect` | terminal | kernel-checked, conditional |
| N37-2 | Mark only the no leaf terminal; do not assume or alter universality. | framework | `node37P13TargetDefect` | terminal | kernel-checked, conditional |
| N37-3 | Preserve all unrelated constructors and the full ledger. | framework | `Node37Stage` | terminal | kernel-checked, conditional |

## Status

Node [37] is kernel-checked but remains conditional/yellow solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. The legacy `ExactHandoff` target-defect record is not used.
