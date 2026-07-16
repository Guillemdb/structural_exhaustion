# Independent cross-review: node 179 long-prefix degree refinement

## Residual-flow ledger

| Incoming branch | Exact accumulated residual | Local data inspected | Retained earlier facts | Node move | Outgoing branches | Consumer |
|---|---|---|---|---|---|---|
| 161 long -> 163 forced prefix -> 164 first-nine collision and CT10 promotion | `P13SameWindowLongPrefixStateLabels` equal to `runP13SameWindowLongPrefixStateLabels`, including its exact routed `SemanticRefinementResidual` | the two literal vertices already selected by node 164 and their two ambient degrees | distinct occurrences, equal degree residues modulo four, equal selected-packing membership, promoted CT10 terminal and exact trace | one full-degree equality decision | exact degree equality; or unequal degrees with equal residues modulo four | new white full D4--D7/CT8 semantic successor |

Node 164 does not carry raw-curvature coordinates, Type A traces, Type B fan
data, or sparse-surplus coordinates.  Consequently the old full D4--D7/CT8
claim is not dependency-ready.  Node 179 is narrowed to the earliest honest
graph-owned refinement and the full semantic claim must move to a new white
successor.  No fact from the incompatible short branch 170--175 is used.

## Execution map and ownership

| Node | Input | Owner | Result | Work |
|---|---|---|---|---|
| 179 | exact node-164 routed residual | `Graph.LongPrefixDegreeRefinement` | `ExactDegreeResidual` or `CongruentDegreeGapResidual` | `2 |V| + 1 <= 2(|V|+1)` |

The reusable classifier and its branch theorems live in `Graph`; the Erdős
file only gates the exact predecessor and instantiates the graph runner.  The
non-Erdős transfer is `Examples.LongPrefixDegreeRefinement`, which exercises
the exhaustive result and both branch-specific runner equations.

## Review verdict

**PASS after review-local repairs** for the narrowed node-179 contract.

- Provenance is exact: the public source contains node 164 together with
  equality to its actual runner.  `exact_ct10_refinement` identifies the
  consumed residual, `exact_ct10_run` identifies the literal CT10 execution,
  and the promoted terminal, exact trace, and first missing
  `responseContexts` class are all re-exposed.
- The two graph observations are not reconstructed: the new
  `p13SameWindowLongPrefixDegree_{first,second}Vertex_exact` and
  `...Degree_exact` theorems identify them with the literal corridor entries
  selected by node 164 and their ambient degrees in `ctx.G.object`.
- The computation evaluates two degrees on the actual retained vertices and
  performs one equality decision.  It enumerates no response, context, state,
  graph, or ambient-universe family.
- Both constructors retain selected-packing membership equality and the exact
  modulo-four equality inherited from node 164.  The exact-degree constructor
  did not initially expose the latter field; the cross-review repaired that
  omission rather than asking consumers to reconstruct it.
- There is no CT8 capability, removal object, response equality, or D4--D7
  claim in the implementation.
- The original transfer fixture was only universally parameterized.  The
  cross-review added an actual execution on the textbook complete graph
  `K_9`; its nine literal vertices take the exact-degree branch and satisfy
  the same local work bound.
- Focused framework, concrete transfer, and Erdős builds pass.  `#print
  axioms` on the runner, exhaustive theorem, Erdős runner, CT10-promotion
  theorem, and literal-degree provenance theorem reports only `propext`,
  `Classical.choice`, and `Quot.sound`; none inherits HSS or a new axiom.

Integration must add the two framework modules and the Erdős module to their
umbrella imports, map node 179 to a new manuscript lemma describing this exact
dichotomy, and move the old `rem:p13-long-prefix-full-semantics` claim to a new
white successor.  The integrator should then add web declaration coverage,
tests, and regenerate the descriptor.

Focused commands run by the independent review:

```text
cd lean
lake build StructuralExhaustion.Graph.LongPrefixDegreeRefinement \
  StructuralExhaustion.Examples.LongPrefixDegreeRefinement

cd examples/erdos_64_eg
lake build Erdos64EG.P13SameWindowLongPrefixDegreeRefinement
lake env lean /tmp/ReviewNode179Axioms.lean
```
