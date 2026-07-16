# Node [193] review: pairwise local separator clause

## Verdict

**READY FOR INDEPENDENT REVIEW.** Node [193] consumes node [190] exactly and
derives only pairwise inequalities from its already proved local incidence
injectivity. The semantic obligation remains unchanged. Node [196] is the sole
white successor.

## Exact flow

`SemanticBottleneckPairwiseClauseSource.node190Exact` identifies the stored
predecessor with the canonical node-[190] runner. The node-[193] result is
indexed by `source.node190.result`, and `resultExact` identifies it with the
graph runner on that same value.

The graph result derives its clause from the exact node-[190] certificate and
copies `first.obligationExact`. Thus it consumes both the retained local
certificate and the still-pending node-[187] routing tag without replacing or
discharging either.

## Exact local clauses

- mismatch and both prefix certificates pass through unchanged; their derived
  clause is only `True` because no additional graph fact follows locally;
- each cubic certificate yields pairwise inequality of its three exact
  boundary vertices and inequality of the internal vertex from each boundary;
- each high certificate yields pairwise inequality of its four exact declared
  endpoints and inequality of the centre from each endpoint.

The proofs use only node [190]'s endpoint injectivity and adjacency (`Adj.ne`).
They introduce no new search, choice of vertices, or semantic premise.

## Semantic boundary and work

Pairwise distinct local endpoints do not imply sparse exit, response equality,
CT3 compatibility/compression, Type-B fan safety, fixed capacities, target
behavior, or closure. None of those certificates is present.

The node performs proof projection only, so visible checks are exactly zero.
It enumerates no vertices, pairs, contexts, responses, colorings, graphs,
types, or ambient universes and accepts no caller Boolean.

## Ownership, transfer, validation

Reusable pairwise clauses live in `Graph.LocalSeparatorPairwiseClause`; the
surplus adapter only follows the exact seven constructors. The non-Erdős
transfer checks cubic boundary/internal inequalities on the branching tree and
high endpoint/centre inequalities on `K5`.

Focused Graph, example, and Erdős builds pass. The scoped forbidden-pattern
scan and diff checks are clean. `#print axioms` reports only standard Lean
axioms locally; the official prefix additionally inherits exactly the
permitted HSS theorem axiom.

Shared integration, WebExport, topology, TeX, README, and implementation-log
files were not edited.

## Independent cross-review

**PASS; no repair required.** A fresh dependent-source audit confirms:

- `SemanticBottleneckPairwiseClauseSource.node190Exact` fixes the stored
  predecessor to the canonical node-[190] runner on the same overload and
  homogeneous audit. The node-[193] result is indexed by that exact
  `source.node190.result`, so its node-[190] certificate cannot be exchanged.
- The graph result is likewise indexed by the full node-[190] result. Its
  `clause` is derived from `first.certificate`, while `obligationExact` is
  copied directly from `first.obligationExact`. This preserves the same
  pending payload/tag equation; it does not merely repeat the obligation's
  constructor name.
- All seven local-projection leaves remain covered. Attachment mismatch and
  both prefix leaves retain their exact node-[190] certificate through the
  result index and receive only `True`. Cubic root/after-edge leaves receive
  the cubic pairwise clause; high root/after-edge leaves receive the high
  pairwise clause.
- Cubic clauses prove only pairwise inequality among the three exact boundary
  vertices and internal-vertex inequality from each boundary. High clauses
  prove only pairwise inequality among the four selected declared endpoints
  and centre inequality from each endpoint. Every proof is a direct use of
  inherited injectivity or `Adj.ne`.
- No adjacency decision or list scan occurs at node [193]; `visibleChecks` is
  definitionally zero. The transfer executes both nontrivial clause kinds on
  the branching-tree and `K5` fixtures and checks both forms of inequality.

Focused Graph/example and Erdős builds pass again. The forbidden-pattern and
diff checks are clean. Trust remains standard for node-local definitions, with
exactly the inherited permitted HSS axiom appearing only at the overall
official endpoint.

No sparse-exit, response, CT3, Type-B, fixed-capacity, target, or closure
certificate is introduced. No ambient vertices, pairs, contexts, graphs,
colorings, types, or universes are enumerated. No successor or shared file was
edited during this review.
