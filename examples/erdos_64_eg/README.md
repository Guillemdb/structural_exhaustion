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

## Current audited status

The status authority is the compiled `formalizedNodeIds` list exported from
`Erdos64EG/WebExport.lean`, not historical progress notes later in this file.
Under the exact-predecessor and complete-obligation policy, the current green
set is nodes `[1]`--`[22]`, `[145]`, `[146]`, `[148]`, and `[149]`. Node `[146]` consumes the
canonical node-[145] ledger, executes the exact `78p13 < n` decision, proves
the denominator-safe `theta`/`tau` equivalence, and retains both original
outgoing payloads with a constant work certificate. Node `[148]` consumes the
literal no payload, retains the exact final hot aggregate, and returns exactly
the original `[149]` or `[150]` residual. Node `[149]` consumes that exact yes
residual and proves the normalized `theta <= theta_win + o(1)` density cap:
the complete finite error has a graph-order-only `o(n log n)` envelope, whose
explicit normalized density term tends to zero. Node `[147]` remains yellow at 4/9:
its arithmetic margin is proved, but the Type-A carrier ledger is not yet
connected. Node `[150]` remains yellow at 8/9: its exact cold-mass bounds,
both printed coefficients, and vanishing normalization error are proved; only
the surviving-cold exclusions and exact near-cubic spine payload for `[151]`
are absent. Conditional Lean support at demoted
nodes remains indexed as proved tasks, while every missing original-paper
producer is displayed separately in the web obligation ledger with
`proved / total` and remaining counts. The immutable Chapter 1 topology is
exactly nodes `[1]`--`[157]`; internal helpers are not proof-diagram nodes.

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
- one CT10 stage covering node `[21]` on the exact bounded node-`[19]`
  constructor: all `196` ordered length-pair candidates are classified and
  exactly `91` are retained; fifteen generated `399 × 399` bit relations are
  rechecked against the public attachment semantics in independent cache
  shards; every safe/flat count is audited against the reusable finite
  bit-relation barrier; the scale-`(1,1)` counts are exactly
  `543958,432672,111286`; and rounding-free integer arithmetic proves
  `2^118 ∏ F_{a,b} < ∏ S_{a,b}`. The strict node-`[19]` constructor is
  preserved unchanged for Part X, and no Boolean-state realization is
  assumed;
- one CT6 stage covering the exact ordered surplus ledger at nodes
  `[127]`--`[128]`, followed by exact per-slot activation from the CT2
  non-bridge theorem. Each slot carries its root return, open-suppression or
  triangular response, and exact `T(p) ∪ Γ(p)` support; the activated schedule
  is the CT6 schedule and has length `σ(G)`;
- one CT15 stage covering the exact baseline-demand definition at node
  `[129]`: it computes the cubic-baseline skeleton count, records the
  canonical empty coordinate family with its full exact deficit, and executes
  the reusable full-rank ledger with a linear check bound. It does not assume
  that this deficit is `O(n)`;
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
- the exact pair-accounting chain at nodes `[130]`--`[141]`: CT15 retains the
  complete free/blocked local-response split, CT9 routes free pairs by their
  first selected port and blocked pairs by the deterministic capacity-token
  priority, the selected `P₁₃` packing proves the exact window-join supply,
  and 25 token--role labels partition every pair once. A reusable classwise
  CT9 decision then returns an actual overloaded fibre with its literal token
  class, or proves `σ²≤(450bmax+1)n`. The two full product scans are bounded
  by `225|V|³` and use no graph, path, matching, or Boolean-state universe;
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
`StructuralExhaustion.Graph.InducedPathWindowLedger`,
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
`StructuralExhaustion.Graph.SurplusCapacityTokenRouting`,
`StructuralExhaustion.Graph.SurplusClasswiseOverload`,
`StructuralExhaustion.Core.FiniteReceiverDischarge`,
`StructuralExhaustion.Core.FiniteBoundaryTransfer`,
`StructuralExhaustion.CT10.ExhaustiveClassification`,
`StructuralExhaustion.CT12.DisjointPacking`, and
`StructuralExhaustion.CT9.ClasswiseTokenLedger`,
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
at node `[18]`. The Part X theorem-bearing endpoint is
`exists_verifiedHomogeneousPatternPrefix`; its predecessor chain retains the complete Type B
post-ledger and sparse-envelope prefixes, implements manuscript node `[126]`,
executes the exact baseline-demand definition at node `[129]`, activates every
CT6 surplus slot through its CT2 return and exact open or triangular local
response, and retains that activation as the exact predecessor of CT15. The
framework-owned endpoint implements nodes `[130]`--`[132]`: it generates
each canonically oriented surplus-slot pair once, scans its exact local
blocker supports, retains the first blocker or a proved clear residual,
constructs one proof-carrying shortest connector between the two exact
response supports, and executes CT15 on precisely the free-pair coordinates.
It then executes the node-`[131]` CT9 route on the identical pair schedule.
The five dispatch roles are the four admitted structural blocker kinds and
`freeAnchor`. Nodes `[133]`--`[136]` consume both exact outputs, close the raw
audit exits on the admitted candidate type, assign every blocked pair its
capacity token, prove the `15p₁₃+σ_W` window identity, and form the exact
25-role complete-pair ledger. Nodes `[137]`--`[139]` and `[141]` execute the
coupled classwise decision: positive excess returns a concrete overloaded
fibre and its unique window/remainder/primitive route; the other side proves
the explicit node-`[138]` quadratic surplus bound. The routed overload is
then consumed by the reusable greedy matching--star extractor at nodes
`[140]`, `[142]`, and `[143]`.

The other dependency-ready boundaries are also executed: node `[19]` makes
the exact squared surplus-scale split after node `[18]`; node `[28]` defines
positive deficiency on the exact node-`[27]` remainder. Nodes `[29]`--`[30]`
prove the exact `15p₁₃+σ_W` boundary-incidence ceiling, its
surplus-adjusted form after subtracting `σ_R`, and the integer wedge
floor. Nodes `[31]`--`[35]` build the literal internal-wedge coordinate family,
prove that its cardinality is exactly `W₂(R)` and at most `n³`, and execute CT15 to the
unconditional full-rank terminal. Nodes `[40]`--`[42]` classify an enlarged
determination support by a boundary-fixing graph embedding and close its
proper-support constructor through the framework CT3 compression theorem,
with the node-`[39]` enlarged output literally typed as the proper/whole input
consumed at node `[40]`, retaining the whole-graph constructor for
node `[43]`. Nodes `[43]`--`[47]` now consume the admitted whole-support
quotient produced by the finite determination certificate. Its conditional
certified-reduction field and minimality force exact injective labels, so the
literal rank-drop identification closes at node `[46]`. The same block derives
the one--three repair identity from
a literal finite connected graph component. Nodes `[78]`--`[80]`
compute the degree-four fan ledger and assigned-certificate split; nodes
`[81]`--`[83]` retain an unresolved exact local entry, a full B2 choice with
its post-ledger split, or a minimal overlap; and node `[75]` charges every
ordinary residual center to its actual assigned surplus. Exactly 126 Chapter 1
nodes are green. Nodes `[84]` and `[144]` close their exact local finite
classifiers. Node `[48]` is the repaired finite curvature/product dichotomy:
only its realized constructor enters entropy, while its open constructor
retains the missing realization and a conditional large-budget consumer.
Node `[49]` then defines the exact real normalized entropy of that supplied
state family, its executable floor-log numerator, and a linear local work
bound without enumerating any ambient graph family.
Node `[50]` performs the paper's entropy threshold as the exact finite split
`n^|R| ≤ N_R^10` or its strict reverse, retaining the same node-`[49]` proof
on both constructors and making one arithmetic comparison.
Node `[51]` consumes only that stored high constructor and proves the total-bit
handoff `(|R|/10) log₂ n ≤ log₂ N_R`; the strict low constructor is preserved
unchanged and no node-`[52]` joint accounting is assumed.
Node `[52]` makes the missing same-context product responsibility explicit.
Its realized constructor combines node `[24]`'s actual global completions with
node `[48]`'s exact state schedule, proves recovery of both coordinates, and
injects the supplied pairs into the literal baseline-skeleton code without
scanning the product. Its open constructor retains the exact missing producers
and reaches the large-budget route only after a separate same-context quarter
budget is supplied; it proves no node-`[54]` closure.
Node `[53]` consumes only node `[50]`'s stored strict-low constructor. The
node-`[48]` telescoping ledger and nonempty terminal fibre give
`A ≤ B*N_R`; symbolic tenth-power transport with `N_R^10 < U` proves
`A^10 < B^10*U`. Thus the reverse small-budget edge is impossible, while the
surviving edge still consumes rather than creates the node-`[55]` quarter
budget. The arithmetic performs zero semantic checks and evaluates no power.
The global grouped fan-mass producer is an internal obligation of the original
node `[84] -> [85]` edge.  The attachment/germ-shape classifier and its
semantic sparse-exit/CT3/Type-B/fixed-cap payload remain internal support for
the original node `[144]`; they are not additional diagram nodes.
The manuscript distinguishes raw quotient proposals from admitted quotients.
Boundary and target mismatches are proposal-audit exits; every non-injective
admitted quotient carries a certified smaller counterexample and is ruled out
by minimality. The preceding
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

The baseline-demand CT15 stage then computes the exact cubic-baseline state
count `choose(choose(n,2),ceil(3n/2))` and its executable integer bit budget.
The canonical empty coordinate family is an unconditional demand with exact
deficit equal to that entire budget. The reusable CT15 profile proves its
full-rank terminal, exact ledger and trace, totality, and linear work bound.
The manuscript and web companion explicitly leave the stronger `O(n)`
deficit estimate to a later verified coordinate construction; it is not a
premise of the current endpoint. The framework profile is independently
reused by the three-switch CT15 fixture.

The pair-response CT15 machinery is independently instantiated on the
textbook edge `K₂` in `MantelExample.CT15EdgeResponses`. Its two labelled
one-vertex supports use the same literal boundaried gluing response and the
same admissible-quotient verified-stage contract.

The independent even-cycle package instantiates the same graph theorem on the
textbook complete bipartite graph `K₃,₄`. Deleting its three degree-four
vertices leaves four isolated degree-three vertices, so the retained
internal-three-core exclusion is proved directly and does not use HSS.

`StructuralExhaustion.Graph.External.HegdeSandeepShashank` is the single
trusted external theorem module. Repository tooling allowlists exactly its
`p13Free_hasPowerOfTwoCycle` declaration and continues to reject every other
axiom or admission.

The Part I window-density frontier is node `[22]`. Node `[21]` verifies the
91 finite curvature barriers and their exact rate floor, but does not imply a
complete Boolean cube. The imported local classifier now separates a proved
complete realization from an explicit missing assignment, and the cold
support proves the exact ambient-cubic 15-stub/13-excess arithmetic plus
G1/G2/G3 terminal adapters. An exact sequential-filtration runner now returns
the first ratio-failing fibre or a telescoping complete ledger without a
caller-selected outcome. The concrete cold producer turns an actual cubic
stub into a canonical deleted-edge return and returns a dyadic hit, a surplus
handoff, or an ambient-finite structural germ. G2 has an exact
context-preserving typed handoff. Nodes `[22]`--`[24]` now implement their
directed handoff responsibilities: the exact density dichotomy, its strict
overflow payload, and its complementary finite-cap payload. The graph-owned
completion/response producer, cross-window commuting account, constant
target-relative germ code (or a sound long-scale route), and target-defect
consumer remain explicit downstream requirements. No numerical packing
ceiling is accepted as an external input.

Node `[158]` is a separate green pointwise branch from node `[21]`: for one
exact selected window it scans the actual outside-vertex-by-thirteen adjacency
system and returns a canonical missing assignment, since the all-true response
would make a four-cycle through path positions 0 and 2. It retains the same
selected window for green node `[159]`. That node executes the graph-owned
degree/stub/corridor route and returns exactly a window-surplus position, a
dyadic root-cycle hit, a first corridor-high event, or a quiet
`ColdStructuralGerm`. The dyadic constructor alone is routed to the existing
one-check CT1 G1 consumer, making node `[155]` green on precisely that branch.
The two surplus handoffs and the quiet germ remain open; the germ has only an
ambient-size support bound. This does not discharge the three realization
producers named by green handoff node `[160]`, the 91-coordinate requirement
edge `[21]`→`[22]`, or any later entropy contradiction.

On node `[159]`'s computed quiet constructor, green node `[161]` performs one
support-length comparison at `Qbase = 4²·13²·2¹³`. This constant is exactly
the normalized D1–D3 state cardinal with an empty additional local-coordinate
type; it is not a D4–D7 completeness assertion. The result retains either the
literal short-support residual or the strict long-support residual. Green node
`[162]` consumes equality with the computed short result, selects the third
declared incidence at its cubic return root, and records exactly whether that
endpoint lies on the supplied support or outside it. Green node `[163]`
consumes equality with the computed long result and embeds the forced first
`Qbase+1` support positions, including the unique overflow index `Qbase`.
Green node `[165]` consumes the exact on-support constructor, scans that
bounded return once, and either closes an accepted power-of-two chord through
the existing CT1 runner or retains the exact strictly shorter deleted-edge
return. Green node `[166]` consumes the exact outside constructor, orients its
one support crossing, and packages the cubic root as a three-leaf shape owning
every root incidence. Green node `[167]` rejoins exactly those two
proof-carrying branches. It selects the shorter return with strict decrease on
the chord branch and the original return with equality on the outside branch,
retaining one outside root incidence, cubic ownership, support at most
`Qbase`, and length at most the original, with zero additional checks. Green
node `[168]` scans that exact return against the union of all
ambient-cubic selected-window supports. It returns either full support
containment or the first oriented membership transition with its exact
boundary stub, outside endpoint, and induced-remainder component. This union
is not the manuscript's selected cold subfamily. Green node `[169]` consumes
the exact computed all-inside result, prepares and stores one ambient-cubic
owner lookup per return vertex, and scans consecutive stored owners. The
single-window result contradicts the original external stub neighbour, so it
retains the first distinct-owner edge and two exact opposite cross-window
tokens. Its work is at most `n² + Qbase*(n+1)`. Green node `[171]` applies a
zero-check typed route to that exact pair. It retains the distinct endpoint
tokens, both exact `crossWindow` subtypes, endpoint windows and positions,
their opposite oriented contributions, and equality of their underlying
literal edge. Green node `[170]` consumes node `[168]`'s exact
first-transition result. One shared computed outside BFS finset drives its
proof-carrying return-exit scan, explicit `WindowIndex × Fin 13` first hit,
distinct second stub, complete duplicate-free incident schedule, true cyclic
`List.next` successor, and declared-order shortest BFS path. Its full visible
ledger, including both BFS computations and the actual token filter, is at
most `50 * localScale^3`.

Green node `[173]` consumes node `[170]`'s exact schedule and independently
computes its declared-order BFS-tree shortest path. Equality to that one
computed path packages the observation rank; no path family is generated,
ordered, or scanned. The two literal degrees, two `Fin 13` offsets, and
connector length project to one genuine `State (Fin 0)`, whose empty local
response retains exactly `MissingD4D7`. Its visible work is exactly `2*n+13`
and at most `15*(n+1)`.

Green node `[171]` is the exact terminal residual of the computed all-inside
branch. It does not assert a repeated owner or second connector.
Green node `[174]` consumes the typed node-`[173]` residual together with
equality to its actual run. Its anchor row is exactly that retained state; all
other rows re-anchor node `[170]`'s complete incident schedule and use its
stored cyclic successor. A collision scan over only those observed local rows
returns either two distinct rows with the same coarse D1–D3 state or a proof
that the schedule length is at most `Qbase`. The state universe is never
enumerated, and visible work is at most `100 * localScale^4`.

Green node `[175]` consumes node `[174]`'s exact result, routes a retained
coarse pair through CT10, or scans only the bounded actual rows and returns a
complete family or first typed missing row. Green node `[180]` eliminates the
impossible complete reconstruction at the actual anchor and retains the exact
coarse or first-missing D4–D7 witnesses. Full compatible-response and CT8
implications pass through green node `[182]`'s fixed clause schedule and remain
white at node `[185]`.
This short first-transition branch is incompatible with the verified long
`[163]`--`[164]` prefix branch, and no edge from `[173]`, `[174]`, or `[175]`
enters `[164]` or its degree-refinement consumer `[179]`. Node `[160]` is green
as an exact proof-level dichotomy: its positive output carries the complete
graph-owned realization/gluing package, while its open output carries that
package's exact absence and the named producers that remain to be built. Only
the realized output enters node `[22]`.
Green node `[48]` consumes the exact node-`[24]` coverage and node-`[47]`
full-rank ledger. It proves the finite surplus-error curvature inequality and
then returns a graph-semantic conditional-fibre realization or the exact open
realization requirement. The realized branch injects its local states into
the labelled baseline-skeleton family; the open branch has only a typed
consumer for a separately proved quarter budget. Neither branch enumerates a
graph family, context universe, subset family, or Boolean cube.
Green node `[164]` inspects only the first nine literal
node-`[163]` prefix occurrences, retains an actual collision in the eight
degree-residue/packing-membership labels, and executes CT10 on those two
occurrences. Its visible work is at most `144*(n+1)+9`; it proves no D4–D7
response equivalence or CT8 removal. Green node `[179]` reads exactly the two
full degree rows and returns equality or a congruent nonzero gap; green node
`[183]` compares exactly nine local adjacency coordinates. Green node `[186]`
extends that scan to exactly the first eighteen coordinates while preserving
the same CT10 obligation. Green node `[189]` extends only through literal
positions 18--26, so the full response consumer remains white at `[192]`.
The current diagram has 193 active nodes. Green is reserved for complete Lean
implementations of the corresponding cells in `original_erdos_64_proof.tex`;
implemented but incomplete original cells are yellow, and all supplemental
nodes above `[157]` are grey. The exact counts are generated from the Lean-owned
crosswalk. Green node `[177]` consumes
node `[144]`'s exact typed trigger and
scans only its `78*p13` attachment coordinates. It returns the first mismatch
or full alignment and one of four stored rooted-germ shapes, retaining an
exact CT10 selection, trace, and the work bound `234*p13 + 7 ≤ 234*n + 7`.
Green node `[178]` consumes all five leaves, retaining mismatch/prefix leaves
and exposing literal cubic/high separator splits. Green node `[181]` performs
the cubic-switch normalization, and green node `[184]` projects exactly its
literal switch data or retained high-center ports. Stronger semantic
implications pass through green node `[187]`'s exact pending-obligation tags,
green node `[190]`'s first fixed-arity incidence clause, and green node `[193]`'s
pairwise local-separator clause; the absent semantic consumer remains beyond
the manuscript boundary. On the component branch, green
node `[185]` focuses the exact D4 head and retains the literal D5--D7 tail;
green node `[188]` emits only singleton graph-derived D4 evaluation requests,
green node `[191]` records the missing graph-local predicate and provenance,
and green node `[194]` retains the resulting evaluator-construction residual
without accepting an evaluator. Green node `[192]` extends the long-prefix
scan only through positions 27--35, and green node `[195]` retains the exact
compatible-response frontier without claiming response semantics. Node `[174]`
proves no full-response repetition, CT8 removal, D4–D7
reconstruction, second connector, cycle, cold-family semantics, bounded-germ
promotion, target closure, CT3 compression, return termination, or density
estimate.

The exact valid node-`[21]` handoff to Part XI is now explicit for the whole
packing. One route entry is computed for every selected window; the actual
thirteen-bit classifier cold residual and same-window node-`[159]` frontier
are retained, and the surplus/dyadic/corridor-high/quiet subledgers partition
exactly `p13` entries. This is not the still-open 91-coordinate completion
system and supplies no entropy or density estimate.

The exported typed workflow is also root-connected: all 98 implemented stages
are reachable from `proof-slice.official`. The explicit composition
links retain the exact node-`[21]` prefix for the whole-packing Part-XI route,
the Type B residual-center ledger for node `[84]`, and the homogeneous-pattern
audit for node `[144]`. A frontend regression test rejects any future orphaned
implemented stage.

The next non-Boolean producer layer is now explicit. A dependent family runner executes the fixed 91-coordinate
symbolic prefix schedule over the exact CT12 selected-window order and returns
the first obstruction or complete per-window ledgers, with envelope
`91*p13`; node `[160]` packages the graph completion and gluing semantics in
its realized constructor and routes exact nonexistence to named downstream
requirements in its open constructor.
Separately, the fixed-skeleton entry schedule computes for every selected
window either its first strict-surplus position or its canonical
ambient-cubic external stub, proving exact coverage, the cubic counts 15 and
13, and quadratic local work. Fixed D4--D7 reconstruction, F2--F4 routing,
and bounded-multiplicity aggregation are still required after node `[24]` for
the dependent Part-IV closure.

Prior F4 supports now use the reusable framework persistent-residual ledger.
Occurrences are primary, so two producer steps remain distinct even when
their event values or declared supports coincide. The graph specialization
performs exact first-hit recognition and proves the negative branch for every
literal occurrence; the older list ledger is only a compatibility
materialization for the existing D6 structural runner. The Erdős adapter
canonically tags the ordinary, decorated, and route-8 schedules and proves
their provenance. That provenance is now the first property in a
`Core.ResidualRefinement.Ledger`: later nodes receive the accumulated state
and add only their new property, while the framework preserves the exact
events, occurrence identities, and every prior proof. This closes the
reusable-ledger design obligation, but not
the causal producer obligation: the current immutable diagram produces the
actual node-`[64]`, node-`[84]`, and node-`[108]` occurrences downstream of
node `[24]`, so pre-node-`[24]` component candidates cannot rigorously populate
the node-`[153]` F4 ledger.

The node-`[24]` Lean boundary now also requires the density statement itself:
`118108581006 * U13 ≤ 1500000000 * n`, in addition to `p13 ≤ U13` and the
strict-quarter budget. A tautological choice `U13 := p13` can no longer be
presented as the manuscript's window-density theorem.

The long-corridor side is now preserved by a branch-indexed pre-CT17 handoff
with its exact support length, checked scale, strict longness proof, and
canonical finite positions. CT17 is not executed until graph theorems supply
the missing target/offset universes, compatibility and value reflection, and
a justified finite scale limit.

Likewise, the first sequential ratio failure now has an exact arithmetic
handoff retaining its computed run, first barrier, and before/after fibres.
It is not presented as CT6, CT7, or CT10: those consumers require semantic
failure data, representatives and contexts, or classified data that the
cardinality inequality does not construct.

The earlier `P13MultiScaleConnectorState` and short-path CT3 prototypes are
now audit-only modules. They scan ambient-size sequence, path, or context
families and therefore are not imported by the production Erdős package and
do not support any green node. The production cold route instead normalizes a
two-boundary prefix to capped boundary degrees, two `Fin 13` window offsets,
thirteen dyadic response bits, and a fixed D4--D7 coordinate alphabet. The
paper-prescribed cold-skeleton producer is structural: it carries a declared
cyclic successor and a proof-carrying canonical component path, without an
ambient attachment or context scan. Its exact remaining obligation is the
graph-derived D4--D7 projection together with packed reconstruction and
all-compatible-context response transport. Until that theorem is proved, the
requirements carried by nodes `[160]`, `[23]`, and `[24]` and the dependent
Part IV closure remain open; the nodes themselves are verified handoffs.

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
