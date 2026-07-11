# CT3 semantic node-to-Lean map

`CT3-v1` has 13 stable nodes, 12 typed edges, and seven exact terminals.

| Semantic node | Contract | Lean owner |
|---|---|---|
| `CT3.entry` | validated `Input` | `CT3/Nodes/Entry.lean` |
| `CT3.decide.scope` | `ScopeCandidate` or `ScopedState` | `CT3/Nodes/Scope.lean` |
| `CT3.certify.equivalence` | `ScopedState → EquivalenceState` | `CT3/Nodes/Equivalence.lean` |
| `CT3.decide.compression` | indexed C2 certificate or `UncompressibleState` | `CT3/Nodes/Compression.lean` |
| `CT3.decide.defect` | C3, CT7, CT12, or `PersistentState` | `CT3/Nodes/Defect.lean` |
| `CT3.decide.table` | indexed C5 or CT8 result | `CT3/Nodes/Table.lean` |

The remaining nodes are the scope, C2, C3, C5, CT7, CT12, and CT8 terminals
owned jointly by `Graph.lean`, `Execution.lean`, and `Theorems.lean`. Every
payload retains the exact equivalence, uncompressible, and persistence indices
that justified its edge.
