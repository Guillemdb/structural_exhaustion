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
- one CT6 stage covering the exact ordered surplus ledger at nodes
  `[127]`--`[128]`, followed by a registered CT6-to-CT9 route that scans
  exactly the surplus slots and separates `σ(G) ≤ 1` from the branch carrying
  two distinct slots; it does not enumerate pairs or claim the later
  free/blocked response semantics;
- a CT1/CT10/CT9/CT7/CT5/CT7 local-port sequence: exact four-cycle avoidance,
  canonical open/triangular selected-port classification, same-centre open
  fibres, a registered overload-to-response route, and an exact two-shoulder
  charge ledger, followed by the exact nonadjacent-endpoint fan-compatibility
  interpretation; every finite universe is graph-owned and polynomially
  bounded, and the CT7 scan is executed only on an actual CT9 overload;
- an all-incident-port CT10 profile at each requested high centre, producing
  a compatible open pair or at least `degree - 2` triangular ports by scanning
  exactly the declared neighbour list and never materializing port pairs;
- a triangular-shoulder CT5 profile with two sites per triangular port,
  proving all four completion-bookkeeping clauses with at most
  `2|V|²+2|V|+2` checks and no path or subset universe;
- a framework-owned CT2-to-return transition and certificate-driven CT1 stage
  for every actual triangular port: the simple path omits the port endpoint,
  restores a cycle of exact length `|Q|+2`, satisfies the Mersenne-predecessor
  exclusion, and exposes the exact four-way initial landing split with one
  certificate check and no path enumeration;
- a graph-owned CT10 first-landing profile over the exact
  `(triangular port × two shoulders) × declared vertices` completion table:
  every actual completion is central, cross-triangular, or outside, every
  other port vertex and noncentral centre neighbour is excluded, and the
  preceding CT1 return is composed with this classifier at a bound of
  `6|V|²+3` checks;
- a graph-owned CT9 cross-shoulder profile for two fixed triangular ports:
  it scans only four shoulder pairs, proves that overload forces a
  degree-at-least-four shoulder (the disjoint alternative is a forbidden
  four-cycle), and otherwise returns the exact capacity-one survivor in at
  most five checks;
- a graph-owned CT5 fan-closure profile for two fixed compatible open ports:
  the Erdős layer supplies the actual `P₁₃` window/remainder partition and
  assigned-incidence predicate, while the framework derives two fan-closed
  ports, four pairwise-distinct oriented carriers, the exact charge trace,
  and totality in exactly ten checks;
- a registered CT5 charge-ledger to CT14 route and graph-owned fan-mass
  profile: CT14 scans the actual cubic-closed-neighbour subtype, retains its
  exact unit mass and multiplicity, proves that a compatible pair injects as
  two distinct members, and derives a positive quarter-deficit numerator with
  a conservative `4|V|²+4|V|+1` audit and linear memory;
- a registered CT14 capacity-to-CT14 refinement and graph-owned hybrid
  incidence profile: every actual cubic-closed neighbour contributes exactly
  two non-centre incidences, four-cycle avoidance proves their endpoints are
  pairwise distinct, CT14 computes the exact window/non-window multiplicities,
  and the resulting half-credit pays the local deficit with at least three
  quarter-units of slack under the explicit marked-fan input `degree ≤ 8`;
  the stored refinement universe has exactly `2c ≤ 2|V|` members and the
  conservative audit is `4|V|²+20|V|+1`;
- an executable `K₄` fixture pinning the length-three rooted return and CT1
  terminal, trace, and check count.

The fixed `P₁₃` computation is a separate cache boundary:
`P13LabelKernel.lean` defines the compact code/profile, and
`P13LabelCertificate.lean` contains the isolated finite-reflection reports.
Normal proof-stage edits therefore reuse the certificate `.olean`. The
verified proof prefix does not store the reported table cardinality or size
histogram, so the native table computation is absent from its theorem
dependency graph. The semantic gap theorem is kernel-checked with `decide`.
The production root does not import `Erdos64EG.Tests`; tests and web export
request that module explicitly.

The reusable implementation is in
`StructuralExhaustion.Graph.MinimumDegreeCycleRouted` and
`StructuralExhaustion.Graph.PackedMinimumDegreeCycle`, together with
`StructuralExhaustion.Graph.InducedPath`,
`StructuralExhaustion.Graph.InducedPathPacking`,
`StructuralExhaustion.Graph.InducedPathAttachment`,
`StructuralExhaustion.Graph.TriangularFirstLanding`,
`StructuralExhaustion.Graph.TriangularCrossShoulder`,
`StructuralExhaustion.Graph.FanClosedPort`,
`StructuralExhaustion.Graph.FanClosedPortMass`,
`StructuralExhaustion.Graph.HybridFanIncidence`,
`StructuralExhaustion.Graph.InducedPathBridge`,
`StructuralExhaustion.Graph.FanWindowCycle`,
`StructuralExhaustion.Graph.TwoWindowCycle`,
`StructuralExhaustion.Graph.P13FanLabelPacking`,
`StructuralExhaustion.Graph.P13MarkedFanLabelPacking`,
`StructuralExhaustion.Graph.CertificateClosedFanCharge`,
`StructuralExhaustion.Graph.AssignedSupportCharge`,
`StructuralExhaustion.Graph.WindowExternalCharge`,
`StructuralExhaustion.Graph.InducedCoreFanReserve`,
`StructuralExhaustion.Graph.FiniteInducedBoundary`,
`StructuralExhaustion.Graph.LowDegreeReceiverRouting`,
`StructuralExhaustion.Graph.HighCenterDeletionCharge`,
`StructuralExhaustion.Core.FiniteReceiverDischarge`,
`StructuralExhaustion.Core.FiniteBoundaryTransfer`,
`StructuralExhaustion.CT10.ExhaustiveClassification`,
`StructuralExhaustion.CT12.DisjointPacking`, and
`StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.CertificateProfile`,
`StructuralExhaustion.Routes.CT1ToCT12`, and
`StructuralExhaustion.Routes.CT5ToCT14`,
`StructuralExhaustion.Routes.CT14ToCT14`,
`StructuralExhaustion.Routes.CT6ToCT9`, and
`StructuralExhaustion.Routes.CT9ToCT7`.
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
`exists_verifiedSparseEnvelopePrefix`; it retains the complete Type B
post-ledger prefix and then implements manuscript node `[126]`. The preceding
Type B block composes the previously
verified marked-fan degree cap with the actual two-port CT14 mass and hybrid
incidence ledgers, deriving the positive deficit and paying capacity rather
than accepting either as input, and projects the resulting endpoint-disjoint
window/non-window ledger to the exact local B1 interface. The framework then
defines the positive-deficit Type B candidate fibre directly from the literal
incidences: every window incidence is mandatory, ordinary-reserve incidences
are forbidden, and selected non-window incidences pay the exact remaining
demand. Candidate finiteness is proof-level and does not evaluate a powerset.
The certificate-closed fibre is likewise defined on the actual neighbour
ports with assigned-incidence quarter weights: `-1` when assigned-closed and
at least `3` when assigned-open. Deletion criticality proves its selected endpoints lie
in `N(h) \ H_X`, and its nonnegative charge is the candidate validity
theorem. The two literal fibres feed the common dependent weighted-selection
adapter, which derives the heterogeneous candidates, their proof-level
finiteness, selected carrier supports, and complete declared carrier
universes. CT12 then proves, for the entire declared center schedule, either a
pairwise-disjoint full choice or a nonempty inclusion-minimal overlap
obstruction in at most one iteration per graph vertex. Reserve-blocked empty
fibres remain visible in the overlap support. Ambient target avoidance,
high-center independence, cubic neighbors, and proper-subfamily choices are
derived for that obstruction. Finally, from only a literal vertex scope and
reserve, the degree-at-least-four center set is graph-derived and the exact
state-space split is proved: an actual high center has no verified local
entry, or all high centers form the complete CT12 family and yield a full
choice or a minimal overlap obstruction. No local-entry or center-completeness
assertion is accepted as a scope field.

The assigned-charge stage then realizes a full choice in literal induced-core
charge. Decorative and window shoulders are handled by an exact external
correction, and selected non-window half-credits are permitted only at
canonical ordinary available core vertices. Every consumed core support is a
subset of its candidate carrier, so CT12 disjointness proves exact
no-double-counting. The framework partitions the counted core into used
vertices, retained high centers, and the remaining core and proves the exact
reduced-ledger identity. Consequently a full disjoint local choice either has
nonnegative net charge or exposes a strictly negative literal remaining core.

The Type A continuation is now connected at its exact graph boundary. The
remaining induced graph is proved `P₁₃`-free, internal-three-core-free, and
subcubic, and the framework proves the `3/7/11` unsaturated receiver theorem.
Crucially, Lean also proves that induced remaining charge equals the raw charge
retained by the Type B identity plus four quarter-units per incidence deleted
with the selected vertices. Therefore the current total state space ends in
nonnegative net charge, an actual saturated receiver, or a strict finite
boundary overload with a literal cut edge and center-or-selected-entry
landing.  Each local selected support has at most 24 vertices, the processed
support has at most 25 vertices per assigned center, and its ambient degree
sum is at most 200 per center.  Consequently every unsaturated negative net
quarter-charge is proved to be at most 800 times the assigned surplus.  No
boundary-transfer premise is accepted as a B2 field.

The official quantitative Type B endpoint is choice-free.
`StructuralExhaustion.Graph.HighCenterDeletionCharge` deletes every actual
high center, bounds the literal center cut, and retains the exact total
overload of the proof-selected `3/7/11` receiver fibres. The Erdős
instantiation proves that the deleted graph is `P₁₃`-free,
dyadic-cycle-free, and internal-three-core-free. For every literal Type B scope
Lean proves, in quarter-units,

```text
-TypeBNet ≤ 21 * assignedSurplus + centerDeletedReceiverOverload.
```

This applies equally on local-entry failure and minimal-overlap branches. The
overload term is the exact Type A continuation, not a supplied certificate or
an assumed charge bound.

The sparse-envelope CT12 stage selects a cubic vertex from deletion
criticality and forms the literal induced complement. The no-proper-core CT2
theorem proves that complement is 2-degenerate. The reusable graph profile
constructs one proof-selected bounded elimination order, and CT12 audits that
finite list in exactly `n-1` iterations. Its sharp local edge count gives
`e(G-v)≤2(n-1)-3`, hence `m≤2n-2`. The generic handshake bridge identifies
the existing CT6 excess ledger with `σ=2m-3n`, and Lean proves the complete
node `[126]` identity `σ=n-6-2λ` for `λ=2n-3-m`. The same profile is
independently instantiated on the textbook triangle in the greedy-coloring
example package.

The independent even-cycle package instantiates the same graph theorem on the
textbook complete bipartite graph `K₃,₄`. Deleting its three degree-four
vertices leaves four isolated degree-three vertices, so the retained
internal-three-core exclusion is proved directly and does not use HSS.

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
