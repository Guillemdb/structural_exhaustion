# Node [49] repair template

## Paper identity

| Field | Value |
|---|---|
| Node | `[49]` |
| Incoming edge | `[48]` |
| Outgoing edge | `[50]` |
| Local responsibility | Project the current residual's compatible global completions to the exact remainder and define `η(R)=log₂|𝒢_real(R)|/|R|`. |
| Retained facts | Exact fixed remainder, compatible-completion state, canonical hot aggregate, and node-[48] cost. |
| New output | The exact realized-state count and symbolic entropy identity. |
| Framework operation | `State.StageNode.mapFocusedBranchNoContinuation`; realized family is `Core.DependentOwnerGlueCapacity.RealizedProjection`. |

## Obligations

| Task ID | Paper assertion | Incoming producer | Lean source | Outgoing edge | Status |
|---|---|---|---|---|---|
| N49-PROV | Consume the literal node-[48] full-rank payload. | `[48]` | `node49P13RemainderEntropy` requires and maps the exact `Node48Stage` leaf | `[50]` | kernel-checked |
| N49-CARRIER | Use exactly the remainder graph obtained by restricting the current compatible completion. | accumulated residual | `node49CanonicalAggregate`; `RealizedProjection` | `[50]` | kernel-checked |
| N49-REALIZED | Every counted remainder state has a witness in the current compatible-completion residual. | framework | `DependentOwnerGlueCapacity.RealizedProjection` | `[50]` | kernel-checked |
| N49-JOINT | The realized remainder choice and all retained hot local choices reglue injectively into the same skeleton code. | accumulated hot aggregate | `node49RealizedRemainderHotCapacityProfile`; `node49_realizedRemainder_mul_hotChoices_le_skeletonCode` | `[52]` | kernel-checked |
| N49-ENTROPY | `η(R)=log₂|𝒢_real(R)|/|R|`. | local definition | `Node49Output.stateCountExact`; `Node49Output.entropyExact` | `[50]` | kernel-checked |
| N49-ROUTE | Replace only node [48]'s live leaf and preserve both handled siblings. | framework | `mapFocusedBranchNoContinuation` | `[50]` | kernel-checked |
| N49-WORK | The node is symbolic bookkeeping with zero semantic scans. | core | `Node49Output.semanticChecksZero`; `node49LocalChecks = 0` | `[50]` | kernel-checked |

## Status

All node-[49] obligations are kernel-checked on the incoming residual. Node
[49] does not create an ambient graph family, assert the later entropy branch,
or decide node [50].
