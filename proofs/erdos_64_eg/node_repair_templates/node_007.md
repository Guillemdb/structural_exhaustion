# Node [7] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [7] |
| Incoming edges | [6] yes -> [7] |
| Outgoing edges | branch terminal |
| Local responsibility | Convert the exact Mersenne-return witness into a power-of-two cycle and close that terminal against inherited counterexample avoidance. |
| Retained branch facts | Node-[5] target algebra and node-[6] return witness. |
| New output | Terminal contradiction on the C1 edge; the exact CT1 avoiding run is the sole live successor of node [6]. |
| CT chain | Framework-owned CT1 public-target closure and avoiding-successor retention. |
| Immediate consumers | terminal only |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N7-PRED | Consume literal node-[6] yes-stage | [6] | `node7PowerOfTwoCycle` requires `Available Node6Stage` | yes->[7] | proved |
| N7-QUERY | Retrieve return witness and target algebra | [5],[6] | CT1 framework continuation retrieves the literal node-[6] stage and its retained node-[5] predecessor | yes->[7] | proved |
| N7-CYCLE | Produce the exact power-of-two cycle and contradict inherited avoidance | [7] | `publicTarget_of_certifiedC1`; `node7CloseTarget` | terminal | proved |
| N7-SURVIVOR | Retain only node-[6]'s literal avoiding run | CT1 | `DependentCertificateFamily.AvoidingSuccessor`; `closePublicTargetContinueAvoidingUsingStage`; `node7_avoids` | no->[8] | proved |
| N7-WORK | Preserve CT1 terminal work evidence | CT1 | `node7_work` | terminal | proved |

## Framework and validation record

- No caller-supplied return certificate or application-owned branch wrapper is accepted here.
- Focused kernel command: `cd examples/erdos_64_eg && lake -Kjobs=1 build Erdos64EG.Node8NoProperCore` (passed through node [7]).
- Dashboard/TeX synchronization: pending.
