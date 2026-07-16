# Node [178] local semantic-consumer review

## Verdict

The old node-[178] claim is not derivable from the exact node-[177] output.
Node [177] retains one attachment mismatch or full attachment alignment plus
one of four rooted-path shapes.  It does not retain an outside distinguishing
context, target-complete quotient, proper-support compression, delocalization
certificate, fan-safety audit, or decorated Type-B envelope.  These are the
premises used by `lem:same-token-bottleneck-routing`; manufacturing any of
them in node [178] would be proof injection or an ambient context search.

The dependency-ready correction is therefore a finite local separator audit.
Node [178] consumes all five exact node-[177] leaves, preserves the mismatch
and two prefix leaves unchanged, and refines both divergence leaves by the
literal separator degree:

| node-[177] leaf | retained local data | node-[178] result | next consumer |
|---|---|---|---|
| attachment mismatch | first failed retained coordinate | identical typed mismatch | node [181] semantic mismatch consumer |
| aligned left prefix | alignment and exact left-prefix tag | identical typed prefix | node [181] CT3/quotient consumer |
| aligned right prefix | alignment and exact right-prefix tag | identical typed prefix | node [181] CT3/quotient consumer |
| aligned root divergence | two actual root incidences | actual-neighbour first third incidence, then cubic/high | node [181] cubic-switch/high-fan consumer |
| aligned after-edge divergence | predecessor and two actual divergent incidences | three pairwise-distinct incidences and one local cubic/high degree test | node [181] cubic-switch/high-fan consumer |

Node [181] remains white and owns the stronger sparse-exit, CT3, Type-B,
fixed-cap, and near-cubic implications.

## Ownership and provenance

- `Graph.RootIncidence` owns both the declared-order third-incidence scan and
  the proof-carrying after-edge incidence/cubic-high split.
- `Graph.SurplusPatternSemanticConsumer` owns the graph-specific adapter from
  the exact `SurplusPatternSemanticBottleneck.Residual`.
- `Examples.SemanticBottleneckConsumer` executes the root-incidence and
  after-edge classifiers on the textbook graph `K₅`; its local degree fixtures
  also cover high and cubic branches on `K₅` and the branching tree.
- `Erdos64EG.Internal.SemanticBottleneckLocalConsumer` is a thin concrete
  instantiation.  Its `previous` field is definitionally the actual
  `semanticBottleneckClassification`; `frontierExact` identifies the retained
  result with the generic classifier on that exact predecessor residual.
- `exists_verifiedSemanticBottleneckLocalConsumerPrefix` extends
  `exists_verifiedSemanticBottleneckClassificationPrefix`; it does not accept
  a classifier result or semantic conclusion as a premise.

Every `Frontier` constructor stores an equality with the source residual tag.
The divergent data are created only while eliminating the actual rooted-path
comparison retained by node [177].  Thus no sibling comparison, reconstructed
path, or look-alike context can enter the result.

The independent review repaired one incidence defect in the initial version:
the after-edge payload had stored three adjacencies but proved only the two
successors distinct.  The final payload is a `RootIncidence.AfterEdge`;
canonical tree-path nodupness proves that the predecessor differs from each
successor, and `RootIncidence.classifyAfterEdge` consumes that certificate.

## Computation and work

The root-divergence branch calls `RootIncidence.classify` on the selected
graph's declared ordered-neighbour list.  Its scan is at most `|V|`.  The
after-edge branch calls `RootIncidence.classifyAfterEdge`, which performs one
supplied-separator degree comparison.  The uniform budget is therefore

```text
checks = |V| + 1.
```

Mismatch and prefix leaves perform no graph search.  No path family, outside
context family, quotient family, subgraph family, graph family, coloring
family, or ambient universe is enumerated.

No new CT is appropriate at this step: node [177] already ran CT10 to produce
the exact finite tag.  Node [178] is ordinary proof-preserving composition
with the public local incidence and degree classifiers; wrapping that fixed
tag in a second CT10 table would add no mathematical operation.

## Trust audit

`#print axioms` reports:

- `Graph.SurplusPatternSemanticConsumer.classify`: `propext`,
  `Classical.choice`, `Quot.sound`;
- `semanticBottleneckLocalConsumer`: the same standard axioms;
- `exists_verifiedSemanticBottleneckLocalConsumerPrefix`: the same standard
  axioms plus the sole permitted Hegde--Sandeep--Shashank theorem inherited
  through the earlier verified prefix.

There is no `sorry`, `admit`, unsafe declaration, new axiom, or caller-supplied
semantic contract in the changed files.

## Focused validation

The following commands pass:

```text
cd lean
lake build StructuralExhaustion.Graph.SurplusPatternSemanticConsumer \
  StructuralExhaustion.Examples.SemanticBottleneckConsumer

cd examples/erdos_64_eg
lake build Erdos64EG.SemanticBottleneckLocalConsumer
lake env lean /tmp/ReviewNode178Axioms.lean
```

Shared imports, TeX, WebExport, generated artifacts, and node-status surfaces
were deliberately left untouched during this parallel task.  Their owner must
integrate this audited block atomically, mark node [178] green, and move the
old semantic statement and arrows to white node [181].
