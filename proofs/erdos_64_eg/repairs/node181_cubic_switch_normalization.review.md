# Node [181] cubic-switch / high-separator normalization review

## Verdict

**PASS** for the narrowed, dependency-ready node-[181] contract.

The advertised sparse-exit, CT3, decorated Type-B, fixed-cap, and near-cubic
conclusions are not consequences of node [178].  The exact predecessor has a
first attachment mismatch, an aligned prefix direction, or a rooted
divergence with a proved cubic/high separator split.  It does not contain a
distinguishing outside context, target-complete quotient, response vector,
fan-safety certificate, decorated fan envelope, or homogeneous-cap ledger.
Those stronger semantic implications remain at white node [184].

## Residual-flow ledger

| Exact node-[178] leaf | Retained data inspected | Node-[181] output | White consumer |
|---|---|---|---|
| attachment mismatch | exact first mismatch evidence | unchanged typed mismatch and source tag equality | [184] mismatch semantics |
| aligned left prefix | exact alignment and left-prefix tag | unchanged typed prefix | [184] CT3/quotient semantics |
| aligned right prefix | exact alignment and right-prefix tag | unchanged typed prefix | [184] CT3/quotient semantics |
| root divergence, cubic | two divergent incidences, classified third incidence, degree (3) | literal `CubicStar.Data` on the exact root | [184] finite switch-response audit |
| root divergence, high | exact root and degree at least (4) | identical high-degree residual | [184] fan-safety / Type-B audit |
| after-edge divergence, cubic | predecessor and two divergent incidences, degree (3) | literal `CubicStar.Data` on the exact separator | [184] finite switch-response audit |
| after-edge divergence, high | exact separator and degree at least (4) | identical high-degree residual | [184] fan-safety / Type-B audit |

Every constructor of `SurplusPatternSemanticNormalization.Result` is indexed
by the exact predecessor residual and frontier.  The Erdős source additionally
stores `node178Exact`, equating its predecessor with the actual
`semanticBottleneckLocalConsumer`.  The result field is equated to the generic
normalizer on that same dependent value.  No sibling path or reconstructed
context can be substituted.

## Ownership and transfer

- `Graph.CubicStar` owns the reusable incidence-to-four-vertex-star
  conversion and its full-neighbourhood theorem.
- `Graph.SurplusPatternSemanticNormalization` owns only the typed adapter from
  the exact node-[178] surplus frontier.
- `Erdos64EG.Internal.SemanticBottleneckSwitchNormalization` is a thin
  concrete instantiation and verified-prefix extension.
- `Examples.SurplusPatternSemanticNormalization` executes the same public
  conversion on two named non-Erdős graphs: `K_5` takes the root-high branch,
  while the five-vertex branching tree takes the after-edge cubic branch and
  checks that its literal star support has cardinality four.

No new CT is appropriate.  Node [178] already performed the only local
searches.  Node [181] is ordinary proof-preserving normalization through
`CubicStar.fromRootBranch` and `CubicStar.fromAfterEdgeBranch`; wrapping this
zero-check conversion in CT10 would add no mathematical classification.

## Computation and trust

The new work count is exactly zero.  The normalizer pattern matches the
already retained cubic/high branch and packages its incidence proofs.  It
does not inspect a new vertex, path, response coordinate, context, quotient,
subgraph, graph, coloring, or ambient universe.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`
for the graph normalizer, both `CubicStar` conversions, and the concrete
Erdős normalizer.  The official verified-prefix endpoint additionally
inherits the sole permitted Hegde--Sandeep--Shashank theorem from earlier
stages.  There is no `sorry`, `admit`, unsafe declaration, or new axiom.

## Focused validation

The following commands pass:

```text
cd lean
lake build StructuralExhaustion.Graph.SurplusPatternSemanticNormalization \
  StructuralExhaustion.Examples.SurplusPatternSemanticNormalization

cd examples/erdos_64_eg
lake build Erdos64EG.SemanticBottleneckSwitchNormalization
lake env lean /tmp/ReviewNode181Axioms.lean
```

Shared umbrella imports, TeX, WebExport, frontend topology, README/log, and
generated artifacts were intentionally left untouched for atomic integration
by their owner.  Integration should mark node [181] green and place every
stronger semantic implication at white node [184].

## Independent cross-review

An independent review replayed the node-[178] dependency cone and confirms
the PASS verdict without changes to the theorem-bearing files.

- `SemanticBottleneckNormalizationSource.node178Exact` identifies the source
  with the actual integrated `semanticBottleneckLocalConsumer`; the normalizer
  is indexed by that source's exact residual and frontier.
- The five node-[178] constructors are exhaustive.  The three non-divergence
  leaves pass through unchanged, while each of the two divergence leaves is
  exhaustively split into cubic and high, giving exactly the seven node-[181]
  constructors listed above.
- Root cubic data consists of the two literal divergent incidences and the
  proof-selected third incidence.  After-edge cubic data consists of the
  predecessor incidence and the two literal divergent successors.  The
  constructors retain all three adjacency proofs, all three pairwise
  inequalities, and degree exactly three.  `support_card` and
  `neighborFinset_eq_boundary` therefore apply to the literal four-vertex
  star, not to an inferred or searched shape.
- `normalize` calls only the two proof-data conversions and performs no new
  finite inspection, so the additional work is definitionally zero.  The
  ambient-neighbour scan exposed elsewhere by `CubicStar.Data` is not invoked
  by this node.
- The non-Erdős transfer reaches a root-high branch on the named complete
  graph and an after-edge cubic branch on the named branching tree, checking
  the latter's four-vertex support.  Generic totality covers the unchanged
  mismatch/prefix leaves and both cubic/high splits.
- Focused builds pass.  The node-local normalizer and cubic-star theorems use
  only `propext`, `Classical.choice`, and `Quot.sound`; the verified-prefix
  endpoint inherits exactly the previously permitted HSS theorem.  No
  `sorry`, `admit`, unsafe declaration, or new axiom occurs.

No sparse-exit witness, CT3 quotient or response equality, decorated Type-B
fan, fixed-cap ledger, near-cubic conclusion, or target closure is present.
Those remain exclusively assigned to the white successor.
