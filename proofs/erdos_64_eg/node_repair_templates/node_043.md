# Node [43] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[43]` |
| Incoming edge | `[41]` no (`Z = G`) |
| Outgoing edge | `[44]` |
| Local responsibility | Record whole-graph delocalization on the exact determination carrier `Z`. |
| Retained facts | Node-[41] whole proof on the equal admitted-candidate carrier and node-[35] exact carrier equality. Node [42] is only an accumulated sibling terminal. |
| New output | `node35.certificate.carrier.IsWhole`. |
| Framework operation | `State.StageNode.continueFocusedBranchNo`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N43-PROV | Consume node [41]'s no constructor directly, never node [42]'s conclusion. | `[41]` | `node43P13WholeGraphDelocalization` requires `Node41Stage` | `[44]` | kernel-checked, conditional |
| N43-CARRIER | The CT15 candidate carrier and the determination certificate carrier are exactly equal. | `[35]` | `Node35CollisionSupportCertificate.carrierExact` | `[44]` | kernel-checked, conditional |
| N43-WHOLE | Transport `IsWhole` across that equality to the exact determination support `Z`. | `[41]` no; `[35]` equality | `Node43Output.certificateCarrierWhole`; `node43Output` | `[44]` | kernel-checked, conditional |
| N43-ROUTE | Preserve the proper sibling and opaque bypass while appending only the whole-carrier bridge. | framework | `FocusedBranchDecisionNoContinuation` | `[44]` | kernel-checked, conditional |
| N43-LEDGER | Retain node [42]'s independently proved proper terminal in the same accumulated run without using it as this edge's predecessor. | framework | `runInitialThroughNode43` extends `runInitialThroughNode42`, while the node executor queries `Node41Stage` | `[44]` | kernel-checked, conditional |
| N43-WORK | Perform no finite scan. | framework | `node43LocalChecks = 0` | `[44]` | kernel-checked, conditional |

## Status

Node [43] is locally kernel-checked but remains partial solely because its
incoming ledger depends on the accumulated node-[21] framework ledger,
`Node23DenseWindowQuietBlockInput`, and
the missing node-[35] collision-support obligation. Its local producer showed no
`sorryAx`. Node [43] proves neither the repair identity nor raw-label
injectivity.
