# CT1 semantic node-to-Lean map

`CT1-v1` has stable semantic identifiers independent of presentation order.
Every branching node returns a proof-carrying constructor for exactly one edge;
the equivalence node is a single-successor certification boundary.

| Semantic node | Consumes | Produces | Lean owner |
|---|---|---|---|
| `CT1.entry` | `Input F` | validated entry contract | `CT1/Nodes/Entry.lean` |
| `CT1.decide.scope` | `Input F` | `ScopeCandidate` or `ScopedState` | `CT1/Nodes/Scope.lean` |
| `CT1.terminal.scope` | `ScopeCandidate` | scope-indexed outcome | `CT1/Execution.lean` |
| `CT1.certify.equivalence` | `ScopedState` | `EquivalenceState` | `CT1/Nodes/Equivalence.lean` |
| `CT1.decide.realization` | `EquivalenceState` | `C1Certificate` or `AvoidingState` | `CT1/Nodes/Realization.lean` |
| `CT1.terminal.c1` | `C1Certificate` | C1-indexed outcome and target proof | `CT1/Execution.lean`, `CT1/Theorems.lean` |
| `CT1.decide.payload` | `AvoidingState` | one of six indexed payloads | `CT1/Nodes/Payload.lean` |
| `CT1.terminal.ct2` | `CT2Payload` | CT2 outcome certified by `HandoffPlan` | `CT1/Execution.lean` |
| `CT1.terminal.ct3` | `CT3Payload` | CT3 outcome certified by `HandoffPlan` | `CT1/Execution.lean` |
| `CT1.terminal.ct4` | `CT4Payload` | CT4 outcome certified by `HandoffPlan` | `CT1/Execution.lean` |
| `CT1.terminal.ct5` | `CT5Payload` | CT5 outcome certified by `HandoffPlan` | `CT1/Execution.lean` |
| `CT1.terminal.ct6` | `CT6Payload` | CT6 outcome certified by `HandoffPlan` | `CT1/Execution.lean` |
| `CT1.terminal.ct17` | `CT17Payload` | CT17 outcome certified by `HandoffPlan` | `CT1/Execution.lean` |

## Contract boundaries

Static target-test vocabulary belongs to `Framework`, and runtime data belongs
to `Input`. The equivalence certificate exposes both implications explicitly.
Its failure is handled before machine admission, so the graph contains no
untyped repair loop.

`AvoidingState` retains the equivalence state, exhaustive realization absence,
and target-avoidance proof. Every downstream payload is indexed by that state.
`Port` and `HandoffPlan` then add consumer acceptance without altering the core
path or raw outcome.

The CT2 terminal is definitionally aligned with its consumer:
`CT2Payload.toInput` returns `CT2.Input F.ct2`, fixes its ambient object to the
CT1 input, and reuses the CT1 target-avoidance proof.

The CT3, CT4, and CT5 terminals likewise carry actual consumer inputs rather
than raw datum placeholders. Their `toInput` adapters expose those inputs, and
their `aligned` fields prove the application-specific relation to the CT1
ambient object and branch state. CT6 and CT17 remain abstract until their
consumer frameworks are formalized.

## Legacy migration

The previous 26-node diagram mixed static declarations, design repair,
persistence prose, payload construction, and consumer boxes with runtime
control. `CT1-v1` moves static declarations into `Framework`, treats failed
equivalence as pre-admission repair, stores persistence in `AvoidingState`, and
collapses payload construction plus routing into one six-constructor decision.
Only the 13 semantic runtime states remain in the executable graph.
