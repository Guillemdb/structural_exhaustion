# Erdős Problem 64 framework example

This independent Lake package exercises the reusable structural-exhaustion
framework on the first reductions of Erdős Problem 64. It depends on Mathlib
4.31.0 and on the framework through `path = "../../lean"`. Framework modules
remain application-independent.

The public proposition in `Erdos64EG/OfficialStatement.lean` is the exact
right-hand side of `Erdos64.erdos_64` in Google DeepMind's
formal-conjectures repository, pinned at commit
`bcaee6031a085e19432540650e1039b7fd1cea36`. It remains in Mathlib
`SimpleGraph` vocabulary. Internal CT adapters carry a proved bridge to that
statement.

The internal ambient type is the framework's `Graph.FiniteObject`: the same
Mathlib `SimpleGraph` together with the explicit `FinEnum`/adjacency data
needed by deterministic search.

The verified proof slice contains:

- a proved equivalence between the finite executable length predicate and
  the official `∃ k ≥ 2, length = 2^k` predicate;
- the manuscript return set `R_e(G)`, the executable Mersenne predicate, the
  fixed-exponent root-edge dictionary, and the exact equivalence between
  target avoidance and disjointness of every return set from the Mersenne set;
- proof-carrying CT1 executions for both an explicit Mersenne return and an
  exact target-avoiding branch, with one-check and zero-check budgets;
- rank-minimal counterexample selection by natural-number well-ordering and a
  registered CT1-avoiding to local-deletion CT2 route;
- lexicographic `(vertices, edges)` minimal selection across finite vertex
  types and the certificate-driven CT2 proof that every proper subgraph has
  minimum degree at most two;
- CT2 over Mathlib `SimpleGraph.Dart`, with finite local dart discovery,
  single-edge deletion, exact edge-count decrease, baseline preservation,
  target transport, the degree-three endpoint theorem, and independence of
  the degree-at-least-four vertices;
- a composed `VerifiedBoundariedReplacementPrefix` constructed from any
  internal counterexample hypothesis, retaining the fixed-vertex
  `VerifiedCT1CT2Prefix` and packed `VerifiedNoProperCorePrefix`;
- the CT3 boundary-degree fibre and context-universality theorems plus literal
  packed-graph gluing: exact vertex/edge arithmetic, locally derived global
  rank decrease, derived minimum-degree preservation, isomorphism-based target
  transport, replacement contradiction, and hereditary target-uncompressibility
  for the explicit nonempty-boundary atom scope; no graph or context universe
  is enumerated;
- one CT1 stage covering diagram nodes `[15]`--`[16]`: the typed avoiding
  branch is literal induced-`P₁₃`-freeness, the isolated HSS external theorem
  converts it to the already forbidden dyadic target, and the forced Mathlib
  induced embedding follows the exact C1 trace with one certificate check;
- one CT12 stage covering node `[17]` and the packing-derived clauses of
  `[25]`--`[27]`: a maximum induced-`P₁₃` packing, maximal saturation, exact
  `|R| + 13p₁₃ = n` partition, a selected-list execution of exactly `p₁₃`
  iterations and bounded by `n`, hereditary `P₁₃`-freeness of `R`, and no
  finite internal subgraph of minimum degree at least three;
- one CT10 stage covering node `[18]`: exact compact enumeration of all
  `2¹³ = 8192` attachment labels, the `399` legal rows and size distribution
  `13,60,122,122,63,17,2`, symbolic equivalence with avoidance of gaps `2`
  and `6`, exact `C_s` and `Ω₂`, an exhaustive typed CT10 run with
  `167792` accounted checks, and a graph theorem placing every actual
  nonempty attachment in the table;
- an executable `K₄` fixture pinning the length-three rooted return and CT1
  terminal, trace, and check count.

The fixed `P₁₃` computation is a separate cache boundary:
`P13LabelKernel.lean` defines the compact code/profile, and
`P13LabelCertificate.lean` contains all five finite-reflection proofs. Normal
proof-stage edits therefore reuse the certificate `.olean`. The production
root does not import `Erdos64EG.Tests`; tests and web export request that module
explicitly.

The reusable implementation is in
`StructuralExhaustion.Graph.MinimumDegreeCycleRouted` and
`StructuralExhaustion.Graph.PackedMinimumDegreeCycle`, together with
`StructuralExhaustion.Graph.InducedPath`,
`StructuralExhaustion.Graph.InducedPathPacking`,
`StructuralExhaustion.Graph.InducedPathAttachment`,
`StructuralExhaustion.CT10.ExhaustiveClassification`,
`StructuralExhaustion.CT12.DisjointPacking`, and
`StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.CertificateProfile`.
The Erdős modules retain only the power-of-two/Mersenne predicates, their
arithmetic equivalences, the fixed `P₁₃` code predicate and constants, the
official-statement bridge, thin profile instantiations, and the concrete `K₄`
fixture. The independent even-cycle package instantiates the graph/CT3/CT12
profiles, while the Mantel package instantiates the same compact attachment
label and CT10 classification machinery at a fixed edge.

`Erdos64EG/CT3.lean` thinly instantiates the framework's
`Graph.PackedBoundariedGluing` profile at minimum degree three and the
power-of-two-cycle target. The framework owns the actual Mathlib graphs,
literal gluing, exact rank and degree proofs, isomorphism transport, typed
runner, totality, and work bound. One CT3 stage covers manuscript nodes
`[11]`--`[14]`: boundary-degree
fibres, context universality, the replacement lemma, and hereditary
target-uncompressibility.

`Erdos64EG/CT1InducedP13.lean` executes one CT1 block over both diagram nodes
`[15]` and `[16]`. `Erdos64EG/CT12InducedP13Packing.lean` adds the exact
packing output, and `Erdos64EG/CT10P13LabelAlgebra.lean` consumes that output
at node `[18]`. The current theorem-bearing endpoint is
`exists_verifiedP13LabelAlgebraPrefix`.

`StructuralExhaustion.Graph.External.HegdeSandeepShashank` is the single
trusted external theorem module. Repository tooling allowlists exactly its
`p13Free_hasPowerOfTwoCycle` declaration and continues to reject every other
axiom or admission.

From the repository root:

```bash
make mathlib-cache
make erdos-example-build
```

Or directly:

```bash
cd examples/erdos_64_eg
lake exe cache get
lake build
```
