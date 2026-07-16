# Node 180: component D4--D7 semantic-readiness prereview

## Residual-flow ledger

| Incoming branch | Exact residual | Local data inspected | Node move | Outgoing residual |
|---|---|---|---|---|
| node 175 coarse repeat | the exact routed pair, including both retained `MissingD4D7Reconstruction` witnesses | the already computed result constructor | retain both typed missing witnesses | coarse semantic block |
| node 175 bounded first missing | the exact bounded ledger and routed first missing row | the already computed result constructor | retain the typed marker at that row | bounded semantic block |
| node 175 bounded reconstructed | a family claiming `D4D7ClausesDerived` on every actual stub | the anchor row only | eliminate the constructor because `D4D7ClausesDerived` has no constructor | impossible |

## Verdict

The advertised full CT8 semantics are not dependency-ready.  Node 175 supplies
no compatible-response alphabet, response function, or certified
smaller-object operation.  Node 180 is therefore implemented as the earliest
unconditional finite branch point.  It consumes the exact node-175 result and
reduces it to the two honest semantic-obstruction branches above.  It does not
enumerate states, contexts, graphs, or any ambient universe; its visible work
is one predecessor-constructor inspection.

The stronger compatible-response / CT8 removal statement must move to new
white node 182.  No response equivalence, removal, target closure, or smaller
object is claimed here.

Framework ownership is split between
`Graph.InducedPathComponentD4D7SemanticReadiness` and its non-Erdos transfer
fixture.  The Erdos module is a thin execution over the literal node-175
output.  Focused framework, transfer, and Erdos builds pass.  `#print axioms`
reports only Lean/mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound`; there is no problem-specific axiom and no HSS dependency.
