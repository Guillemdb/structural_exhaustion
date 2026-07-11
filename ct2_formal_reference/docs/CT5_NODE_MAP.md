# CT5 semantic node-to-Lean map

`CT5-v1` has 11 stable nodes, 10 typed edges, and five exact terminals.

| Semantic node | Contract | Lean owner |
|---|---|---|
| `CT5.entry` | validated local-family `Input` | `CT5/Nodes/Entry.lean` |
| `CT5.decide.scope` | `ScopeCandidate` or `ScopedState` | `CT5/Nodes/Scope.lean` |
| `CT5.certify.locality` | `LocalityState` | `CT5/Nodes/Locality.lean` |
| `CT5.decide.deficit` | CT11 deficit or `LocalLedgerState` | `CT5/Nodes/Deficit.lean` |
| `CT5.certify.summation` | `SummationState` | `CT5/Nodes/Summation.lean` |
| `CT5.decide.comparison` | C4, exact CT4 ledger, or CT14 residual | `CT5/Nodes/Comparison.lean` |

The terminal nodes are scope, CT11, C4, CT4, and CT14. `CT4Payload.toInput`
fixes both the ambient object and branch state definitionally.
