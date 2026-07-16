# Node 186 extended local-clause alignment review

## Verdict

**PASS (independently cross-reviewed, no code repair required)** for the
narrowed node-186 contract.  Complete D4--D7 responses and any CT8 consumer
remain white node 189.

## Residual-flow ledger

| Exact node-183 leaf | Retained input | Node-186 move | Exact output |
|---|---|---|---|
| first-nine mismatch | typed first hit and its preceding aligned prefix | no new predicate evaluation | identical inherited mismatch |
| first-nine aligned | exact alignment on positions 0--8, literal long support, exact two node-164 vertices | compare adjacency on positions 9--17 in declared order | first second-block mismatch with its preceding second-block alignment, or exact alignment on both nine-position blocks |

Both node-179 degree branches remain nested in the exact node-183 source.  No
degree equality is interpreted as response equality.  The node-164 CT10
`responseContexts` promotion is retained as a field of the concrete node-186
result.

## Provenance

`P13SameWindowLongPrefixExtendedClauseSource.node183Exact` equates its
dependent predecessor with the actual
`runP13SameWindowLongPrefixLocalClauseAlignment`.  The graph source projects
that result's `classification` and proves equality with the generic node-183
runner by rewriting with `node183Exact`.  Its nested local source still stores
the exact node-179 degree result and execution equality.

The P13 long constructor proves the identical corridor has more than
`Q_base` entries.  Since `Q_base` is far greater than 18,
`p13SameWindowLongPrefix_firstEighteen` supplies literal positions 0--17; no
new support, path, or graph is selected.

The cross-review also compiled direct checks that
`(supportPosition source i).val = i.val + 9` and that every such value lies in
`[9,18)`.  Thus the second block neither overlaps positions 0--8 nor reaches
beyond position 17.

## Local clause semantics

The second-block coordinate type is `Fin 9`.  Coordinate `i` denotes literal
support index `i + 9`.  At that vertex the graph-owned profile compares only

```text
Adj(first retained vertex, support[i + 9])
Adj(second retained vertex, support[i + 9]).
```

`SecondMismatch.sound` proves the returned coordinate differs, and
`SecondMismatch.prefixExact` proves every earlier second-block coordinate
agrees.  `SecondAligned.exact` proves agreement for all nine second-block
coordinates.  Combined with the retained node-183 `Aligned`, the final
constructor therefore means exactly first-eighteen local adjacency alignment.
It does not mean complete compatible-response equality.

## Practicality and ownership

An inherited mismatch performs zero new checks.  The uniform ledger charges
two adjacency evaluations at each of nine second-block coordinates, hence at
most 18 new checks and `18 <= 18 (|V| + 1)`.  The runner enumerates no ambient
vertex, response, context, state, path, graph, coloring, or Boolean-function
universe.

Finite first-disagreement machinery remains in `Core`; the support-index and
adjacency profile lives in `Graph.LongPrefixExtendedClauseAlignment`; the
Erdős file contains only the exact predecessor gate, concrete first-eighteen
arithmetic, retained CT10 provenance, and thin runner wrapper.

`Examples.LongPrefixExtendedClauseAlignment` independently executes the same
runner and checks its three exhaustive leaves, mismatch soundness, aligned
semantics, and work bound.

The inherited-mismatch equation was separately compiled: whenever the exact
node-183 classification is `firstMismatch mismatch`, the node-186 graph
runner returns `inheritedMismatch mismatch` with the identical dependent
payload and performs no second-block predicate decision.

## Trust and no-CT8 audit

The reviewed files define no response-context universe, D4--D7 family,
response-equivalence theorem, exact-type table, removal operation, or
`Core.SmallerObject`.  No CT8 conclusion is claimed.

The field named `responseContexts` is only the retained equality showing that
the nested exact CT10 run promoted the *class label*
`SemanticClass.responseContexts`.  It is not a response-context enumeration,
realization, equality theorem, or CT8 input.

Focused `#print axioms` checks report only `propext`, `Classical.choice`, and
`Quot.sound`; there is no HSS dependency, new axiom, `sorry`, `admit`, or
unsafe declaration.

## Validation

Passed:

- `lake build StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment StructuralExhaustion.Examples.LongPrefixExtendedClauseAlignment`
- `lake build Erdos64EG.P13SameWindowLongPrefixExtendedClauseAlignment`
- focused trust and forbidden-token audit
- `git diff --check`

Shared umbrella imports, tests, TeX, web topology, documentation, counts, and
generated artifacts were intentionally left for integration.
