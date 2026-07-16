# Node 189 third-block local-clause alignment review

## Verdict

**PASS (independently cross-reviewed, no code repair required)** for the exact
node-189 contract.  Full compatible-response semantics and any CT8 consumer
remain exclusively white node 192.

## Residual-flow ledger

| Exact node-186 leaf | Retained data | Node-189 action | Exact output |
|---|---|---|---|
| inherited first-block mismatch | node-183 first hit and its prefix theorem | no new check | identical first-block mismatch |
| second-block mismatch | first-nine alignment, second-block first hit, and its prefix theorem | no new check | identical first and second evidence |
| first-eighteen alignment | first- and second-block alignment, exact two collision vertices, and literal long support | scan adjacency only at support positions 18--26 | first third-block mismatch with preceding third-block alignment, or alignment on all first 27 positions |

All node-179 degree data and the exact node-164 CT10 `responseContexts`
promotion remain nested in the source.  The concrete node-189 result retains
the CT10 proof as an explicit field.  Neither degree equality nor bounded
adjacency alignment is interpreted as complete response equality.

## Provenance

`P13SameWindowLongPrefixThirdBlockClauseSource.node186Exact` identifies the
dependent predecessor with the actual node-186 runner.  The graph source uses
that result's `classification` and proves its equality with
`LongPrefixExtendedClauseAlignment.run` by rewriting with `node186Exact`.
The nested source retains node 183 and node 179 execution equalities.

The actual node-163 long-support inequality yields at least 27 entries of the
same literal corridor.  `p13SameWindowLongPrefix_firstTwentySeven` derives
this by the already-proved support and scale equalities; it neither selects a
new path nor materializes the full `Q_base + 1` prefix.

The cross-review compiled direct checks that
`(supportPosition source i).val = i.val + 18` and that every such value lies
in `[18,27)`.  Hence the scan neither overlaps the first 18 positions nor
reaches beyond literal position 26.

## Local semantics and computation

The third coordinate block is `Fin 9`; coordinate `i` denotes literal support
position `i + 18`.  The only predicates are adjacency from each of the two
retained collision vertices to that literal support vertex.

The mismatch residual is a `FiniteSearch.FirstHit`, so it proves both the
actual differing third-block coordinate and exact agreement before it.
The aligned residual proves agreement for every coordinate in the block.
Together with the retained earlier blocks, the final constructor states
exactly first-27 local adjacency alignment.

Pre-existing mismatch leaves perform zero new checks.  The uniform upper
ledger charges two adjacency evaluations at each of nine new coordinates:
18 checks, bounded by `18 (|V| + 1)`.  No ambient vertex, response, context,
state, graph, path, coloring, or Boolean-function universe is enumerated.

## Ownership and transfer

The reusable finite first-hit scan remains in `Core`.  The graph-owned offset,
literal-coordinate semantics, branch preservation, and work ledger live in
`Graph.LongPrefixThirdBlockClauseAlignment`.  The Erdős module contains only
exact predecessor gating, fixed-constant support arithmetic, concrete
provenance projection, and a thin runner wrapper.

`Examples.LongPrefixThirdBlockClauseAlignment` independently executes the
same runner and checks all four leaves, mismatch soundness, aligned semantics,
and the work bound.

Both passthrough equations were separately compiled.  An inherited
first-block mismatch returns the identical `FirstMismatch`, and an inherited
second-block mismatch returns the identical first-alignment and
`SecondMismatch` payloads.  Neither case invokes the third-block decision.

## Trust and scope

Focused `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`; there is no HSS dependency, new axiom, `sorry`, `admit`, or
unsafe declaration.

The reviewed files define no D4--D7 response family, response equivalence,
exact-type table, removal function, `Core.SmallerObject`, or CT8 execution.

The retained field named `responseContexts` proves only that the nested exact
CT10 run promoted the class label `SemanticClass.responseContexts`.  It does
not construct or enumerate response contexts and is not a CT8 capability.

## Validation

Passed:

- `lake build StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment StructuralExhaustion.Examples.LongPrefixThirdBlockClauseAlignment`
- `lake build Erdos64EG.P13SameWindowLongPrefixThirdBlockClauseAlignment`
- focused trust and forbidden-token audit
- `git diff --check`

Shared imports, web export, topology, TeX, README, and implementation ledger
were intentionally not edited.
