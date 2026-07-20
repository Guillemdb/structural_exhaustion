# Node [55] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[55]` |
| Incoming edge | `[53] --no--> [55]`, after node [54] terminalizes the other leaves |
| Outgoing edge | `[56]` |
| Local responsibility | Name the literal complementary large-budget leaf as Residual C; add no inequality. |
| Retained facts | Node-[50] low proof, node-[53] large proof, node-[24] density facts, and the complete accumulated ledger. |
| New output | None; the exact focused leaf is the residual. |
| CT/framework chain | Zero-copy `State.StageNode.usingStage` on the framework-owned focused cursor. |
| Immediate consumer | Node `[56]`. |

## Obligations

| Task ID | Original-paper assertion | Incoming ledger producer | Local Lean declaration/framework run | Outgoing edge | Status |
|---|---|---|---|---|---|
| N55-PROV | Consume exactly node [53]'s no constructor after node [54], not either terminal sibling. | `[53]`, `[54]` | `Node55ResidualC := Node54Active`; `node55P13LargeBudgetResidual` | `[56]` | kernel-checked, conditional |
| N55-LARGE | Preserve the exact complementary inequality `forced <= remaining`. | `[53]` | `FocusedBranchNestedNoActive.innerProof` | `[56]` | kernel-checked, conditional |
| N55-DENSITY | Leave node [24]'s window-density theorem in the one ledger; do not copy or rederive it. | `[24]` | accumulated framework state | `[56]` | kernel-checked, conditional |
| N55-THIN | Introduce no predecessor field, handoff, checkpoint, or application residual wrapper. | framework | `Node55Stage` is definitionally the node-[54] focused stage | `[56]` | kernel-checked, conditional |
| N55-WORK | Perform zero checks. | framework | `node55LocalChecks = 0` | `[56]` | kernel-checked, conditional |

## Status

Partial with its zero-copy implementation kernel-checked; inherited missing
producers remain to be discharged.
Node [55] is deliberately a zero-copy paper occurrence: the strict-quarter
net cap belongs only to node [56].
