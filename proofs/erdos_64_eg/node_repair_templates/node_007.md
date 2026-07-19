# Node [7] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [7] |
| Incoming edges | [6] yes -> [7] |
| Outgoing edges | branch terminal |
| Local responsibility | Convert the exact Mersenne-return witness into a power-of-two cycle. |
| Retained branch facts | Node-[5] target algebra and node-[6] return witness. |
| New output | Branch-local target-cycle certificate. |
| CT chain | Framework continuation of CT1's target branch. |
| Immediate consumers | terminal only |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N7-PRED | Consume literal node-[6] yes-stage | [6] | `node7PowerOfTwoCycle` requires `Available Node6Stage` | yes->[7] | proved |
| N7-QUERY | Retrieve return witness and target algebra | [5],[6] | CT1 framework continuation retrieves the literal node-[6] stage and its retained node-[5] predecessor | yes->[7] | proved |
| N7-CYCLE | Produce the exact power-of-two cycle | [7] | `publicTarget_of_certifiedC1`; `node7_cycle` | terminal | proved |
| N7-WORK | Preserve CT1 terminal work evidence | CT1 | `node7_work` | terminal | proved |

## Framework and validation record

- No caller-supplied return certificate is accepted here.
- Focused kernel command: `lake build Erdos64EG.Node7PowerOfTwoCycle`.
- Dashboard/TeX synchronization: pending.
