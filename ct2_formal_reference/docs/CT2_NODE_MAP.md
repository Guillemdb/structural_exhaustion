# CT2 semantic node-to-Lean map

`CT2-v2` uses semantic identifiers whose meaning is independent of display
order. Each decision consumes one staged state and returns a proof-carrying
inductive result. Its constructor determines the unique outgoing edge and
carries the complete state or terminal payload required at the destination.

| Semantic node | Consumes | Produces | Lean owner |
|---|---|---|---|
| `CT2.entry` | `Input F` | validated `Entry.Contract F` | `CT2/Nodes/Entry.lean` |
| `CT2.decide.interface` | `Input F` | `ScopeCandidate` or `BoundedState` | `CT2/Nodes/Interface.lean` |
| `CT2.terminal.scope` | `ScopeCandidate` | `RawOutcome … .scope`, then `Outcome … .scope` | `CT2/Execution.lean` |
| `CT2.decide.deletion` | `BoundedState` | `DeletionWitness` or `DeletionCriticalState` | `CT2/Nodes/Deletion.lean` |
| `CT2.terminal.c2.deletion` | `DeletionWitness` | deletion-indexed C2 outcome and contradiction | `CT2/Execution.lean`, `CT2/Theorems.lean` |
| `CT2.decide.replacementCandidate` | `DeletionCriticalState` | `CandidateState` or `SurvivorState` | `CT2/Nodes/ReplacementCandidate.lean` |
| `CT2.decide.context` | the selected `CandidateState` | `CandidateContextCertificate` or `ContextCT3Payload` | `CT2/Nodes/Context.lean` |
| `CT2.terminal.c2.replacement` | candidate plus its certificate | replacement-indexed C2 outcome and contradiction | `CT2/Execution.lean`, `CT2/Theorems.lean` |
| `CT2.terminal.ct3.context` | `ContextCT3Payload` | CT3 outcome certified by `HandoffPlan` | `CT2/Execution.lean` |
| `CT2.decide.survivor` | `SurvivorState` | `CriticalityCT10Payload` or `ResponseCT3Payload` | `CT2/Nodes/Survivor.lean` |
| `CT2.terminal.ct10.criticality` | `CriticalityCT10Payload` | CT10 outcome certified by `HandoffPlan` | `CT2/Execution.lean` |
| `CT2.terminal.ct3.response` | `ResponseCT3Payload` | CT3 outcome certified by `HandoffPlan` | `CT2/Execution.lean` |

All source paths in the table are relative to `StructuralExhaustion/`. The
corresponding namespaces are `StructuralExhaustion.CT2.Nodes.*` for node APIs,
`StructuralExhaustion.CT2.Graph` for graph indices, and
`StructuralExhaustion.CT2` for shared types, execution, and theorems.

## Exact transition ownership

The 11 constructors of `Graph.Edge` are the authoritative transitions. An edge
stores the evidence returned by the source node; `Graph.Path` permits a next
edge only when its source index is the previous edge's target index. The
interpreter constructs the path while matching the node result, so a transition
label, branch witness, terminal index, and outcome cannot drift independently.

`CorePlan` contains exactly the five decision-node plans. `Port` and
`HandoffPlan` form a separate acceptance layer. Both CT3 payload variants carry
an actual `CT3.Input F.ct3` together with an alignment certificate; CT10 remains
abstract until that tactic is formalized. A public `Outcome` cannot be
constructed without the appropriate consumer-acceptance proof.

## Legacy migration

The former numbered graph mixed static resources, proof obligations, runtime
decisions, and handoff packaging. The semantic graph removes that ambiguity:

| Previous nodes | `CT2-v2` disposition |
|---|---|
| `N01`, static parts of `N02`, `N07` | typed entry and `Framework` resources |
| decision part of `N02`, `N03` | interface decision and scope terminal |
| `N04`, `N05`, `N06` | deletion decision and its two evidence-bearing exits |
| `N08`, `N09`, `N10` | candidate search, candidate certification, replacement terminal |
| `N11`, `N12`, `N14` | one certified CT3 context terminal |
| `N13`, `N15` | uncompressible state and survivor decision |
| `N16`, `N18` | one certified CT10 terminal |
| `N17`, `N19` | one certified CT3 response terminal |

Numbered identifiers remain useful only as historical migration references;
they are not accepted as current graph IDs.
