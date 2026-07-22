# Node 13: Replacement Lemma

## Immutable Paper Contract

- diagram node `[13]`: replacement lemma
  (`original_erdos_64_proof.tex` line 583);
- direct incoming edge: `[12] -> [13]`;
- direct outgoing edge: `[13] -> [14]`;
- table item `[13]`: replacement dominance, citing `\cref{lem:replacement}`
  (`original_erdos_64_proof.tex` line 1099);
- `\cref{lem:replacement}` states that if `G = X \oplus_T Y`, where `X`
  is a proper atom, then a smaller `T`-boundaried graph `X'` satisfying
  `X' \preceq_T X`, the same boundary-degree profile, no internal
  power-of-two cycle, internal minimum degree at least `3`, and strict
  lexicographic decrease would make a smaller counterexample, contradicting
  minimality (`original_erdos_64_proof.tex` lines 5602-5632).

## Normalized Replacement Contract

The legacy kernel implementation realizes the paper replacement strategy with
a normalized outside context: boundary--boundary edges of the decomposition
are owned by the atom side.  In Hypostructure this is the Graph-owned predicate
`OutsideContext.NoBoundaryEdges`, packaged with a proper atom as
`Graph.NormalizedProperBoundariedAtom`.

Graph derives the zero-overlap consequences from that normalized context and
converts a normalized replacement certificate to the generic replacement
certificate consumed by the existing minimality proof.  Node 13 therefore has
no application-owned overlap residual, no node-local routing, and no manual
data-management obligation.

## Mandatory Contract

| Field | Value |
|---|---|
| Node ID | 13 |
| Direct incoming edges | 12 |
| Direct outgoing edges | 14 |
| Literal incoming stage | `HypostructureErdos64EG.Node12Stage` |
| Inherited facts | Node 4 minimal counterexample context, preserved through Node 12 by `node4ContextAtNode12Query` |
| Local responsibility | Replacement contradiction for same-interface proper atom replacements |
| New payload | Normalized `Graph.NormalizedAtomReplacementCertificate` contradiction |
| CT/Core/domain executor | `Graph.executeFocusedNormalizedAtomReplacementCounted` over `Core.Residual.ProofProjection` |
| Complementary residuals | None |

## Implementation Evidence

- New framework module:
  `hypostructure/Hypostructure/Graph/Replacement.lean`.
- Public framework declarations:
  - `Graph.NormalizedProperBoundariedAtom`;
  - `Graph.NormalizedAtomReplacementProfile`;
  - `Graph.NormalizedAtomReplacementCertificate`;
  - `Graph.NormalizedAtomReplacementCertificate.toAtomReplacementCertificate`;
  - `Graph.NormalizedAtomReplacementCertificate.impossible`;
  - `Graph.executeFocusedNormalizedAtomReplacementCounted`;
  - `Graph.focusedNormalizedAtomReplacementQuery`;
  - `Graph.AtomReplacementCertificate`;
  - `Graph.AtomReplacementCertificate.gluedReplacement_smaller`;
  - `Graph.AtomReplacementCertificate.impossible`;
  - `Graph.executeFocusedAtomReplacementCounted`;
  - `Graph.focusedAtomReplacementQuery`.
- New framework fixture:
  `hypostructure/Hypostructure/Fixtures/GraphReplacement.lean`.
- New EG facade:
  `examples/hypostructure_erdos_64_eg/HypostructureErdos64EG/Node13.lean`.
- New parity module:
  `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node13.lean`.

## Status

| Gate | Result |
|---|---|
| Kernel | Fresh direct source: `HypostructureErdos64EG.Node13` |
| Parity | Checked normalized legacy/new surfaces; legacy has the older no-overlap-aware shape |
| Mathematics | Closed: Graph derives overlap and baseline transfer from the normalized context contract used by the legacy implementation |
| Work | Captured by `node13Counted_work_bounded` and `node13_work_bounded` |
| Trust | No new authored axioms; public endpoints use `[propext, Classical.choice, Quot.sound]` |
| Web | `generated/hypostructure/web/snapshot.json` after regeneration |

## Validation

- `lake env lean Hypostructure/Graph/Replacement.lean`;
- `lake build Hypostructure.Graph.Replacement`;
- `lake build Hypostructure.Fixtures.GraphReplacement`;
- `lake env lean HypostructureErdos64EG/Node13.lean`;
- `lake build HypostructureErdos64EG.Node13`;
- `lake build HypostructureParity.Erdos64EG.Node13`.
