# CT4 semantic node-to-Lean map

`CT4-v1` has 11 stable nodes, 10 typed edges, and five exact terminals.

| Semantic node | Contract | Lean owner |
|---|---|---|
| `CT4.entry` | validated ledger `Input` | `CT4/Nodes/Entry.lean` |
| `CT4.decide.scope` | `ScopeCandidate` or `ScopedState` | `CT4/Nodes/Scope.lean` |
| `CT4.certify.assignment` | canonical `AssignmentState` | `CT4/Nodes/Assignment.lean` |
| `CT4.decide.availability` | CT13 witness or `TotalAssignmentState` | `CT4/Nodes/Availability.lean` |
| `CT4.decide.fibres` | CT9 overload or `BoundedFibreState` | `CT4/Nodes/Fibres.lean` |
| `CT4.decide.comparison` | indexed C4 certificate or CT14 residual | `CT4/Nodes/Comparison.lean` |

The terminal nodes are scope, CT13, CT9, C4, and CT14. Canonicality is a
single-successor certification boundary; totality and fibre boundedness are
separate indexed states.
