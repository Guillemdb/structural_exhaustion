# Node [16] repair template

| Field | Value |
|---|---|
| Incoming edges | [15] yes -> [16] |
| Outgoing edges | branch terminal |
| Local responsibility | Apply the Hegde–Sandeep–Shashank theorem to obtain a target cycle on the P13-free branch. |
| Retained facts | Literal node-[15] yes-stage and inherited minimal counterexample facts. |
| New output | Branch-local target-cycle theorem followed by contradiction with inherited target avoidance. |
| CT chain | `StageNode.closeDependentDecisionYes` on node [15]'s literal yes constructor. |
| Immediate consumers | terminal only |

## Obligations

| Task ID | Assertion | Producer | Evidence | Edge | Status |
|---|---|---|---|---|---|
| N16-PRED | Consume literal Node15 yes-stage | [15] | `Erdos64EG.Internal.node16HSSContinuation` (`Node15Stage` ledger query contract) | yes->[16] | proved; kernel checked |
| N16-HSS | Apply only the declared HSS theorem to produce the target cycle | [16] | `Erdos64EG.Internal.node16_hss_target` | terminal | proved; kernel checked relative to the sole HSS theorem |
| N16-CLOSE | Close only the yes constructor against the inherited target-avoidance proof | [16], framework | `node16_hss_closure`, `node16HSSContinuation` | terminal | proved; kernel checked relative to the sole HSS theorem |
| N16-WORK | Preserve proof-only terminal accounting | framework | `node16LocalChecks_eq_zero` | terminal | proved; kernel checked |

Forbidden: proving or importing node-[17] packing closure.
