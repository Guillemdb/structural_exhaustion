# Node [4] repair template

## Paper identity

| Field | Value |
|---|---|
| Node ID | [4] |
| Incoming edges | [2] yes -> [4] |
| Outgoing edges | [4] -> [5] |
| Local responsibility | Choose the lexicographically minimal counterexample prescribed by the paper. |
| Retained branch facts | Exact positive counterexample certificate. |
| New output | Minimal-counterexample context and its defining minimality certificate. |
| CT chain | Framework minimal-counterexample selection/profile. |
| Immediate consumers | [5] |

## Obligations

| Task ID | Paper assertion | Producer | Lean evidence | Edge | Status |
|---|---|---|---|---|---|
| N4-PRED | Consume literal node-[2] yes-stage | [2] | `node4CounterexampleQuery`; `runInitialThroughNode4` | yes->[4] | proved |
| N4-SELECT | Execute lexicographic minimal selection | [4] | `Core.StageNode.selectMinimalCounterexample`; `node4MinimalSelection` | [4]->[5] | proved |
| N4-MIN | Retain the exact minimality certificate | [4] | `Node4Output`; `runInitialThroughNode4_minimal` | [4]->[5] | proved |
| N4-LEDGER | Append all node-local minimality facts once | framework | `BranchResult.mapYesStage`; `StageNode.derive` | [4]->[5] | proved |

## Framework and validation record

- The node may not reconstruct its source from theorem-root arguments.
- Output must be the minimal context only, not a copied predecessor wrapper.
- Focused kernel command: `lake build Erdos64EG.Node4MinimalSelection` from `examples/erdos_64_eg`.
- Dashboard/TeX synchronization: pending.
