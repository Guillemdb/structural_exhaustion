# Nodes [25]--[26] obligation ledger

| Task | Manuscript obligation | Exact Lean evidence | Status |
|---|---|---|---|
| 25.1 | Consume the literal corrected node-[24] payload. | `VerifiedP13Node25LargeRemainder.previous`, `previousExact`, `VerifiedP13Node24FiniteDensityHandoff.node25` | proved |
| 25.2 | Retain the identical node-[21] CT12 packing and remainder. | `coverage`, `coverageExact`, `remainder` | proved |
| 25.3 | Prove the exact packing/remainder partition and finite remainder floor. | `VerifiedP13RemainderResidual.exactPartition`, `VerifiedP13Node25LargeRemainder.large` | proved |
| 25.4 | Retain remainder and componentwise induced-P13 freeness. | `VerifiedP13RemainderResidual.remainderFree`, `componentwiseFree` | proved |
| 25.5 | Derive the numerical large-remainder estimate from node [24] on the same graph. | `thirteen_le_order`, `ratio_ge_main_sub_oOne` | proved |
| 25.6 | Perform no new graph scan. | `p13Node24To26LocalChecks_polynomial` with zero checks | proved |
| 26.1 | Carry exactly node [25]'s residual across the Part-I/Part-II panel boundary. | `VerifiedP13Node26RemainderContinuation`, `VerifiedP13Node25LargeRemainder.node26` | proved |

Nodes [25] and [26] are fully implemented. Node [26] introduces no new graph,
packing, remainder, hypothesis, or case split.
