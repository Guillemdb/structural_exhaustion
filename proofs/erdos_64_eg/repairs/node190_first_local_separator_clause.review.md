# Node [190] review: first local separator clause

## Verdict

**PASS (independently reviewed).** Node [190] consumes node [187]'s exact
pending payload and obligation tag. It proves only fixed-arity incidence facts
already forced by that payload. Node [193] is the sole white successor.

## Exact predecessor consumption

`SemanticBottleneckFirstClauseSource.node187Exact` identifies the stored value
with the canonical node-[187] runner. The result is indexed by the exact
`source.node187.pending`; its `resultExact` field identifies it with the graph
runner on that same pending value.

The graph `Result` constructs its certificate from `pending.retained` and
separately proves
`pending.obligation = required pending.retained`. Thus both halves of the
node-[187] residual are consumed: neither the payload nor its routing tag can
be silently replaced.

Independent inspection also checked the predecessor classifier itself. Its
seven constructors map exactly to `sparseExit`, `fixedCaps`, `fixedCaps`,
`ct3`, `typeB`, `ct3`, and `typeB`, in the same order as the seven literal
node-[184] projections. The node-[190] adapter neither reclassifies a leaf nor
changes that obligation ledger.

## Seven-leaf certificate ledger

- attachment mismatch and both aligned-prefix leaves retain their exact tag
  equalities and evidence unchanged;
- cubic-root and cubic-after-edge leaves expose the exact three boundary
  vertices, injectivity, and adjacency to the projected internal vertex;
- high-root and high-after-edge leaves expose positions `0,1,2,3` in the same
  declared neighbour schedule, injectivity of those ports, adjacency of all
  four endpoints to the same centre, and endpoint injectivity.

The high construction uses `4 <= degree center` together with the exact
declared-neighbour-list length theorem. It does not choose four vertices from
an ambient universe or scan pairs of ports.

## Semantic boundary

The certificates do not prove sparse exit, response equality, a boundaried
piece, CT3 compression, Type-B fan safety, fixed capacities, target behavior,
or closure. In particular, four distinct incident endpoints do not by
themselves constitute Type B. Node [193] must consume these literal clauses
and separately establish any stronger semantics.

## Framework ownership and transfer

`Graph.LocalSeparatorFirstClause` owns reusable cubic and high incidence
certificates. `Graph.SurplusPatternFirstSemanticClause` owns only the typed
seven-leaf adapter. The Erdős file is a thin exact-source instantiation.

The non-Erdős transfer uses the existing branching-tree cubic projection and
the `K5` high projection. It verifies cubic boundary adjacency/injectivity and
four high-port endpoint adjacencies/injectivity.

## Local work and validation

The node inspects one already-computed constructor and projects at most four
fixed declared port positions. Its visible bound is the constant four. It
enumerates no ambient vertices, pairs, contexts, response maps, colorings,
graphs, finite types, or universes, and accepts no caller Boolean.

Focused builds pass:

```text
lake build StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause \
  StructuralExhaustion.Examples.SurplusPatternFirstSemanticClause
lake build Erdos64EG.SemanticBottleneckFirstClause
```

The only replayed warnings are pre-existing unused-variable warnings in
`SurplusPatternCoarseRouting` and `SurplusPatternSemanticBottleneck`; neither
file is owned by node [190].

The scoped scan finds no `sorry`, `admit`, `unsafe`, new axiom,
`Finset.univ`, or `Set.univ`; diff checks are clean. Trust inspection reports
only standard Lean axioms for node-local definitions. The official endpoint
additionally inherits exactly the permitted HSS theorem axiom.

No theorem-bearing repair was required by the independent review.

Shared integration, WebExport, topology, TeX, README, and implementation-log
files were intentionally not edited.
