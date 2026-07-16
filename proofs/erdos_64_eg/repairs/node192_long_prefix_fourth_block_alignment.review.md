# Node 192 fourth-block local-clause alignment review

## Verdict

**PASS (independently cross-reviewed, no code repair required)** for the exact
node-192 contract.  Strong compatible-response and CT8 semantics remain
solely at white node 195.

## Exact branch ledger

Node 192 consumes the exact node-189 result.  Its first-, second-, and
third-block mismatch constructors pass through with all preceding alignment
and first-hit evidence unchanged.  Only the first-27-aligned constructor
evaluates a new block.  It compares adjacency from the same two retained
collision vertices to literal corridor positions 27--35 and returns either:

- a first fourth-block mismatch, including exact agreement before that hit; or
- alignment on the fourth block, together with the retained first three block
  proofs, hence exact local adjacency alignment on positions 0--35.

No mismatch leaf is discarded or recomputed.

## Provenance

`P13SameWindowLongPrefixFourthBlockClauseSource.node189Exact` equates the
stored dependent predecessor with the actual node-189 runner.  Its graph
source projects that exact classification and rewrites the equality to the
generic third-block runner.  The nested source still retains the actual node
186, node 183, and node 179 execution equalities.

The actual long-support inequality, together with node 163's exact scale and
support identities, proves the identical corridor contains at least 36
positions.  The proof does not materialize the full `Q_base + 1` prefix.

The cross-review compiled `supportPosition.val = coordinate.val + 27` and the
range `27 <= supportPosition.val < 36`, so the scan is exactly positions
27--35 and is disjoint from the retained first 27 positions.

The concrete result explicitly retains the node-164 CT10
`responseContexts` promotion, and the graph source exposes the exact node-179
degree result.  Neither fact is restated as an author premise.

## Locality and work

The new coordinate type is `Fin 9`; coordinate `i` maps to literal support
index `i + 27`.  The only two predicates at that coordinate are adjacency
from the first and second retained vertices to the literal support vertex.

Inherited mismatch branches cost zero new checks.  The uniform bound charges
two adjacency decisions at nine coordinates, at most 18 checks and therefore
`18 <= 18 (|V| + 1)`.  No ambient vertex, response, context, state, path,
graph, coloring, or Boolean-function universe is enumerated.

## Ownership and transfer

The reusable first-hit machinery remains in `Core`.  Literal offset indexing,
branch preservation, semantics, and work accounting live in
`Graph.LongPrefixFourthBlockClauseAlignment`.  Erdős code contains only exact
predecessor gating, fixed support arithmetic, retained provenance, and a thin
runner wrapper.

`Examples.LongPrefixFourthBlockClauseAlignment` independently executes the
runner and checks all five leaves, mismatch soundness, aligned semantics, and
the work bound.

All three inherited equations were compiled directly.  First-, second-, and
third-block mismatches return their identical dependent payloads, including
all preceding alignment proofs, without invoking the fourth-block decision.

## Trust and scope

Focused builds pass.  `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`; the reviewed dependency has no HSS use,
new axiom, `sorry`, `admit`, or unsafe declaration.

The files define no D4--D7 response family, complete response equivalence,
exact-type table, removal function, `Core.SmallerObject`, or CT8 execution.

The retained `responseContexts` field is only the nested exact CT10 promotion
class equality.  It neither constructs nor enumerates response contexts and
does not provide a CT8 capability.

Shared imports, web export, topology, TeX, README, and implementation log were
intentionally not edited.
