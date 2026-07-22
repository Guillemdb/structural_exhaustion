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

## Boundary-Overlap Residual

The current checked graph model uses unrestricted union gluing.  Under this
semantics, local boundary-degree equality alone does not determine glued
boundary degrees when both the atom and the outside context own boundary
edges.  This is the existing reviewed issue:

- `migration/hypostructure/issues/0001-eg-node13-boundary-overlap.md`;
- `migration/hypostructure/decisions/0006-graph-boundary-overlap.md`.

Therefore this packet does not mark the literal paper Node 13 obligation as
mathematically closed.  It adds the reusable framework-owned, overlap-aware
replacement executor and records the missing overlap-preservation premise as
a typed metadata obligation.

## Mandatory Contract

| Field | Value |
|---|---|
| Node ID | 13 |
| Direct incoming edges | 12 |
| Direct outgoing edges | 14 |
| Literal incoming stage | `HypostructureErdos64EG.Node12Stage` |
| Inherited facts | Node 4 minimal counterexample context, preserved through Node 12 by `node4ContextAtNode12Query` |
| Local responsibility | Replacement contradiction for same-interface proper atom replacements |
| New payload | Overlap-aware `Graph.AtomReplacementCertificate` contradiction |
| CT/Core/domain executor | `Graph.executeFocusedAtomReplacementCounted` over `Core.Residual.ProofProjection` |
| Complementary residuals | Boundary-overlap preservation needed to recover the literal paper lemma |

## Implementation Evidence

- New framework module:
  `hypostructure/Hypostructure/Graph/Replacement.lean`.
- Public framework declarations:
  - `Graph.AtomReplacementCertificate`;
  - `Graph.AtomReplacementCertificate.gluedReplacement_smaller`;
  - `Graph.AtomReplacementCertificate.impossible`;
  - `Graph.executeFocusedAtomReplacementCounted`;
  - `Graph.focusedAtomReplacementQuery`.
- New EG facade:
  `examples/hypostructure_erdos_64_eg/HypostructureErdos64EG/Node13.lean`.
- New parity module:
  `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node13.lean`.

## Status

| Gate | Result |
|---|---|
| Kernel | Fresh direct source: `HypostructureErdos64EG.Node13` |
| Parity | Checked normalized legacy/new surfaces; legacy has the older no-overlap-aware shape |
| Mathematics | Open against the literal paper Node 13 contract because overlap-count preservation is still a recorded residual |
| Work | Captured by `node13Counted_work_bounded` and `node13_work_bounded` |
| Trust | No new authored axioms; public endpoints use `[propext, Classical.choice, Quot.sound]` |
| Web | `generated/hypostructure/web/snapshot.json` after regeneration |

## Validation

- `lake env lean Hypostructure/Graph/Replacement.lean`;
- `lake build Hypostructure.Graph.Replacement`;
- `lake env lean HypostructureErdos64EG/Node13.lean`;
- `lake build HypostructureErdos64EG.Node13`;
- `lake env lean HypostructureParity/Erdos64EG/Node13.lean`.
