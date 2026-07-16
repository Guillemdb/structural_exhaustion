# Erdős Problem 64 implementation state

This ledger records the Lean-checked proof content in
`examples/erdos_64_eg` as of 2026-07-15.

The current seventy-eight-node boundary is represented by eight branch-complete,
predecessor-linked endpoint theorems:

- `Erdos64EG.Internal.exists_verifiedSurplusScaleSplitPrefix` for node `[19]`;
- `Erdos64EG.Internal.routeSurplusScaleThroughCurvature_exhaustive` for the
  exact split whose bounded constructor is discharged at node `[21]` and
  whose strict constructor remains the Part-X residual;
- `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix` for node
  `[28]`;
- `Erdos64EG.Internal.exists_verifiedP13CurvaturePrefix` for nodes
  `[29]`--`[35]`;
- `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix` for nodes
  `[40]`--`[42]`;
- `Erdos64EG.Internal.exists_verifiedP13GlobalRankClosurePrefix` for the
  admitted whole-support closure at nodes `[43]`--`[47]`;
- `Erdos64EG.Internal.exists_verifiedTypeBResidualCenterLedgerPrefix` for
  nodes `[75]` and `[80]`--`[83]`; and
- `Erdos64EG.Internal.exists_verifiedHomogeneousPatternPrefix` for nodes
  `[140]`, `[142]`, and `[143]`.

For example, the homogeneous-pattern endpoint has the public type:

```lean
(object : Object V) → Baseline object → ¬ Target object →
  ∃ ctx : Core.MinimalCounterexampleContext
      packedStaticInput.problem packedStaticInput.Target,
    packedStaticInput.problem.rank ctx.G ≤
        packedStaticInput.problem.rank
          (Graph.PackedFiniteObject.pack object) ∧
      VerifiedHomogeneousPatternPrefix ctx
```

Natural-number well-ordering selects a counterexample minimal in the
manuscript order `(number of vertices, number of edges)`. The verified output
contains:

- the exact edge-rooted Mersenne CT1 avoiding execution;
- the no-proper-core certificate-driven CT2 stage;
- the registered CT1-to-local-deletion CT2 result;
- deletion criticality and independence of the vertices of degree at least
  four; and
- the CT3 boundaried-replacement stage: boundary-degree fibres, universal
  context response, the replacement contradiction, and hereditary
  target-uncompressibility; and
- the CT1 induced-`P₁₃` stage: the exact avoiding execution, HSS closure,
  forced induced embedding, C1 execution, totality, and constant work bound;
  and
- the CT12 induced-`P₁₃` packing stage: maximum cardinality, maximal
  saturation, an exhausted selected-list execution, the exact
  `|R| + 13 p₁₃ = |V(G)|` partition, hereditary `P₁₃`-freeness of the
  remainder, and absence of every finite internal subgraph of minimum degree
  at least three; and
- the CT10 induced-`P₁₃` attachment-label stage: compact exact coding of
  all `8192` subsets, symbolic equivalence between the code test and the
  manuscript gap test, the complete `399`-row table with size distribution
  `13,60,122,122,63,17,2`, the exact `C_s` and `Ω₂` relations, and proof
  that every actual nonempty attachment in the selected graph belongs to the
  accepted table; and
- the CT10 node-`[21]` multi-scale curvature stage: the exact bounded
  node-`[19]` residual is retained; `196` candidate length pairs are
  exhaustively classified and exactly `91` accepted; fifteen fixed
  `399 × 399` relation tables are audited bit-for-bit in independent shards;
  every accepted safe/flat count is rechecked against the reusable
  `Core.FiniteBitRelationBarrier` profile; the existing scale-`(1,1)` counts
  `543958,432672,111286` are recovered; and the exact integer certificate
  proves `2^118 ∏F < ∏S`, with no logarithm, graph-family, or Boolean-product
  realization in the theorem dependency graph; and
- the exact remainder-curvature stage at nodes `[29]`--`[35]`: every unit of
  node-`[28]` positive deficiency is injected into the selected-window
  incidence ledger; its exact cardinality is `15p₁₃+σ_W`; the reusable
  wedge kernel proves `W₂(R) ≥ 3|R|-2def⁺(R)`; the literal coordinate
  family consists of a remainder center and a canonical unordered pair of
  its internal neighbors; its cardinality is exactly `W₂(R)`; and CT15
  reaches the full-rank ledger with no surviving admitted rank drop; and
- the proper-delocalization route at nodes `[40]`--`[42]`: an enlarged
  certificate records its connected proper support, original-support
  boundary-fixing embedding, strict rank growth, and exact quotient
  realization. The reusable graph route composes the node-`[39]` enlarged
  output directly with the proper/whole input type; the proper constructor yields
  a literal target defect or executes the existing certified CT3 compression,
  while the whole-graph constructor is retained unchanged for node `[43]`;
- the whole-support audit at nodes `[43]`--`[47]`: one supplied quotient is
  split into a literal context defect, exact injective labels, or the explicit
  response-preserving non-injective residual for which no certified closed
  representative has been constructed.  The route assumes no representative;
  node `[46]` records its absence.  Independently, the reusable graph theorem
  derives `s = p - 2 + 2β - σ` from the literal finite connected component,
  and the textbook `K₄` transfer instantiates the same theorem;
- the CT6 ordered surplus stage: one scan of the declared vertex order,
  a first-failure predicate for a non-cubic neighbour of a high centre,
  deletion-critical closure of that failure branch, the exact
  `Σ_v (d(v)-3)` active ledger, and a dependent excess-slot family of the
  same cardinality.
- the CT12 sparse-envelope stage at node `[126]`: deletion criticality selects
  a cubic vertex, the CT2 no-proper-core theorem makes its literal complement
  2-degenerate, and CT12 audits the proof-selected elimination order in
  exactly `n-1` iterations. The graph layer proves
  `e(G-v) ≤ 2(n-1)-3`, hence `m ≤ 2n-2`, and the exact handshake bridge gives
  `σ=2m-3n=n-6-2λ` for `λ=2n-3-m`.
- the CT15 baseline-demand stage at node `[129]`: the exact cubic-baseline
  state count and integer bit budget are computed from `n`; the canonical
  empty coordinate family has exact deficit equal to that full bit budget;
  CT15 certifies its complete full-rank ledger, exact trace, totality, and
  linear work bound. No linear deficit estimate is assumed.
- the completed activation block at nodes `[127]`--`[128]`: each exact CT6
  surplus slot is connected to the CT2 non-bridge output, its deleted-root
  return, its open-suppression or triangular response, and the exact local
  support `T(p) ∪ Γ(p)`. The activated schedule is the CT6 schedule and has
  length exactly `σ(G)`.
- the CT15 free/blocked pair-response block at nodes `[130]`--`[132]`: every
  unordered pair in the exact activated schedule occurs once; the reusable
  core ledger gives the exact disjoint partition; every blocked pair retains
  its first local witness; every free pair retains one shortest connector;
  and the admitted-response profile executes CT15 with the exact full-rank
  terminal, trace, soundness, totality, and polynomial work proof.
- the CT9 total pair route at node `[131]`: every scheduled pair enters one
  exact first-port/product-role fibre. The dispatch alphabet has the four
  admitted structural blocker kinds plus `freeAnchor`. A blocked pair retains
  its canonical first hit and all earlier failed candidates for node `[134]`;
  a free-anchor fibre member is proved blocker-free, has the displayed first
  selected port, and retains the shortest connector and both activation
  supports for the primitive-carrier audit at node `[143]`.
- the CT9 capacity-token block at nodes `[133]`--`[136]`: the admitted blocker
  candidate type closes both raw quotient-audit exits; every blocked pair is
  assigned one deterministic window, remainder-surplus, or primitive token;
  the selected induced-`P₁₃` packing gives the exact
  `15 p₁₃ + σ_W` window-incidence supply; and the unchanged complete pair
  collection is partitioned exactly once among 25 total token--role labels.
  The exact token supply is bounded by `9n`, and the complete audit uses at
  most `225n³` checks.
- the coupled classwise CT9 block at nodes `[137]`--`[139]` and `[141]`: for
  every fixed threshold triple, the exact complete pair count is compared
  with the literal 25-role class capacity. Positive excess returns an actual
  overloaded token--role fibre and its unique window/remainder/primitive
  class route. The other side proves the unconditional local estimate
  `σ² ≤ (450 bmax + 1)n`. This computation also uses at most `225n³` checks
  and does not depend on Boolean-product realization or a baseline-deficit
  estimate.
- the CT9 surplus-pair availability stage: the registered CT6-to-CT9 route
  consumes the actual active-ledger residual, preserves the identical branch
  context, and scans exactly the surplus-slot list; its bounded branch proves
  that at most one slot exists, while overload supplies two distinct slots.
- the CT1 four-cycle-avoidance stage and its graph-owned consequences: every
  high-centre neighbourhood is a matching, and two nonadjacent neighbours
  have no common neighbour outside the centre;
- the CT10 open/triangular classification of the exact canonical surplus-slot
  list, with a quadratic primitive-check bound;
- the CT9 centre-fibre refinement of open selected ports, returning either a
  same-centre open pair or a pointwise capacity-one certificate, without
  enumerating pairs;
- the registered `CT9.residual.overload->CT7` route, which preserves the
  bounded CT9 branch and compares endpoint adjacency responses only when an
  actual overload residual exists; and
- the CT5 shoulder-pair ledger: one `Unit` witness per selected slot certifies
  its two actual non-centre shoulders, and the exact charge ledger totals
  `2 * |P_slot|`.
- the graph-owned CT7 open-pair interpretation: for the exact pair already
  returned by the CT9 overload route, four-cycle avoidance proves the full
  fan-compatible shoulder predicate whenever the endpoints are nonadjacent;
  endpoint adjacency is retained as a separate downstream branch.
- the graph-owned all-incident-port CT10 profile: each requested high centre
  scans exactly its neighbour schedule and yields a compatible open pair or
  at least `degree - 2` triangular ports, with a linear local work bound and
  no materialized pair universe.
- the graph-owned triangular-shoulder CT5 profile: two sites per triangular
  port, first completion endpoints from the declared vertex order, all four
  shoulder-completion clauses, an exact charge trace, and a quadratic bound
  without path or subset enumeration.
- the graph-owned bridge-contraction CT2 profile: a hypothetical bridge is
  contracted by deleting one endpoint name, the framework proves strict
  vertex-rank decrease, minimum-degree preservation, and same-length lifting
  of every simple cycle, and the constant-work CT2 contradiction proves that
  every dart is non-bridging.
- the graph-owned triangular-port CT1 profile: the framework converts the
  CT2 non-bridge theorem into one simple deleted-edge return, derives the
  shoulder path in `G-x`, reconstructs the exact `|Q|+2` cycle, proves the
  Mersenne-predecessor exclusion and four-way initial landing split, and
  validates the proof-carrying certificate with one check.
- the graph-owned triangular first-landing CT10 profile: the explicit
  shoulder-site/vertex table is classified as central, cross-triangular, or
  outside; the graph theorem excludes all other fan-core and centre-neighbour
  endpoints, and the framework composes the result with the exact CT1 return
  while retaining trace validity, totality, and a `6|V|²+3` work bound.
- the graph-owned cross-shoulder CT9 profile: for two distinct triangular
  ports the exact four shoulder pairs form one capacity-one fibre; an
  overload either shares a shoulder and proves degree at least four or gives
  a forbidden four-cycle, while the surviving cubic branch has the exact
  bounded terminal and at most five checks.
- the graph-owned fan-closed-port CT5 profile: a problem supplies only its
  window side, disjoint remainder side, assigned-incidence predicate, and two
  compatible open ports. The framework derives both fan-closure statements,
  exact window/non-window support classes, four distinct oriented carriers,
  the charge trace, totality, and a ten-check bound. The Erdős instantiation
  uses the literal maximum-`P₁₃` packing complement.
- the framework-owned `CT5.residual.chargeLedger->CT14` route and graph-owned
  fan-closed mass profile: the route preserves the complete branch context and
  materializes CT14's empty trigger. The CT14 universe is the executable
  subtype of actual vertices satisfying adjacency, cubicity, remainder
  membership, and assignment of every non-center incidence. A compatible pair
  injects into this set, forcing mass at least two and quarter-deficit numerator
  at least `k-3 > 0`; no claimed count is accepted.
- the framework-owned `CT14.residual.capacity->CT14` refinement and
  graph-owned hybrid incidence profile: the member universe is exactly
  `cubicClosedNeighbor × Bool`, hence has `2c` elements; each member denotes
  one literal non-centre graph incidence, four-cycle avoidance proves endpoint
  injectivity, binary CT14 labels partition it into exact window and non-window
  multiplicities, and two quarter-units per incidence pay the deficit
  `4c+k-11` with at least three quarter-units of slack when the marked-fan
  branch supplies `k ≤ 8`.
- the graph-owned direct fan-window CT1 profile: exact ordered-segment support
  bounds prove that the one-segment centre-crossing walk and the two-segment
  interlacing walk are literal Mathlib simple cycles. The finite violation
  type is equivalent to the manuscript arithmetic clauses, every violation
  constructs one target certificate, and the selected target-avoiding branch
  proves every closed pair direct-cycle-free through a zero-check CT1 run.
  The formal statement explicitly records `h ∉ V(P)`, which is necessary for
  the centre-crossing cycle to be simple; the manuscript now separates the
  ordinary remainder-side case from packed-window handoff centers.
- the graph-owned two-window CT1 profile: an orientation-independent bridge
  follows the unique segment between arbitrary labelled positions in each of
  two induced windows. Vertex-disjoint window supports make the two bridge
  tails disjoint, so their concatenation is a literal simple cycle of length
  `4 + |i-j| + |a-b|`. Target avoidance gives the exact manuscript exclusion
  through the same zero-check certificate-driven CT1 interface.
- the graph-owned certificate-marked fan CT9 profile: the application supplies
  the manuscript's legal nonempty label map on the actual neighbour ports and
  pairwise scale-two compatibility. The framework chooses one representative
  per label, maps representatives to a cached eight-slot cover of the thirteen
  path positions, proves the slot labelling injective, and derives
  `degree h ≤ 8` from the exact bounded CT9 execution. The runtime scan is only
  eight fibres times the actual degree; neither the 8192-code universe nor any
  family of labels is enumerated.
- the graph-owned non-singleton marked-fan CT9 refinement: two distinct
  positions in one actual marked label block two exact representative slots.
  After erasing that fan port, CT9 assigns capacity zero to those slots and
  capacity one to the other six, so the remaining family has size at most six
  and the original fan has degree at most seven. The `13³` blocked-slot table
  and `8²` capacity identity are native-checked once in the isolated cached
  position module.
- the graph-owned certificate-closed CT14 charge ledger: it scans exactly the
  actual fan ports, sums the decidable cubic-closed indicator to obtain `c`,
  sets the open count to `k-c`, and verifies the exact quarter-charge identity
  `(11-4k)-c+3(k-c)=11-k-4c`. The manuscript branch condition
  `4c+k≤11` therefore yields nonnegative closed-neighbourhood charge; the
  conclusion is not a contract field.
- the composed positive-deficit marked-fan entry: two actual assigned,
  compatible fan-closed ports inject into the literal cubic-closed subtype;
  the already verified marked-fan CT9 theorem derives `k≤8`; and the existing
  CT14 mass and hybrid-incidence profiles derive `c≥2`, `4c+k-11>0`, and an
  endpoint-disjoint half-credit ledger that pays the deficit with at least
  three quarter-units of slack. No degree cap, count inequality, deficit sign,
  or capacity conclusion is accepted as a contract field.
- the framework-owned local-ledger projection of that CT14 stage: its literal
  incidence universe has size `2c`, the endpoint map is injective, the
  window/non-window multiplicities partition the universe, and total and
  non-window credit pay the exact manuscript demands. This is the third B1
  alternative after the already excluded exit branches, rather than an
  application-supplied assertion.
- the graph-owned positive-deficit Type B candidate fibre: the item universe
  is the exact `2c` literal incidence list from local B1, every window
  incidence is mandatory, every ordinary-reserve incidence is forbidden, and
  selected non-window incidences must pay the exact CT14 remainder. Candidate
  validity is a definition, not a contract field. The all-incidence candidate
  is constructed from the verified B1 inequality whenever the reserve is
  locally free. Logical finiteness is proved by a subtype injection into
  `Finset`; no powerset is evaluated.
- the graph-owned certificate-closed Type B candidate fibre: its items are
  the actual neighbour ports, each selected weight is the exact
  assigned-internal-degree charge `11-4(1+a)`, cubic-closed means `a=2` and
  weight `-1`, and open members have weight at least `3`. The required amount
  is the negated center charge `4k-11`. Reserve-used vertices are forbidden.
  Deletion criticality derives that every selected endpoint has degree three
  and hence lies outside `H_X`; the CT14 charge theorem constructs the
  complete-neighbour candidate under local reserve-freeness.

The endpoint accepts only the internal graph, its minimum-degree-three proof,
and target avoidance. It accepts no CT outcome, reduction conclusion,
minimality theorem, route result, or author-supplied closure contract.
The Hegde--Sandeep--Shashank theorem used at node `[16]` is the repository's
sole explicitly trusted external theorem declaration.

## Official boundary

`Erdos64EG.OfficialStatement` is the pinned Mathlib `SimpleGraph`
formulation: every finite graph of minimum degree at least three contains a
simple cycle of length `2 ^ k` for some `k ≥ 2`.

The internal executable boundary is established by:

- `PowerOfTwoLength`, whose exponent is searched in `Fin (length + 1)`;
- `powerOfTwoLength_iff`, proving equivalence with the unbounded exponent
  statement;
- `staticInput`, instantiating `Graph.MinimumDegreeCycle.StaticInput` at
  minimum degree three; and
- `target_iff_official_conclusion`, identifying the internal target with the
  official conclusion on the same Mathlib graph.

`Graph.FiniteObject` adds an explicit `FinEnum` vertex schedule and adjacency
decision procedure to the Mathlib graph. These data determine local machine
order and do not define a separate graph representation.

## Current proof-flow execution map

| Manuscript section and nodes | Prior verified input | CT/profile | Verified output | Work bound |
|---|---|---|---|---|
| `def:mersenne-return-set`, `lem:return-equivalence`, nodes `[5]`–`[7]` | Official internal graph and baseline | CT1 target-certificate profile | Exact cycle/return equivalence, C1 execution from a supplied return, and typed avoiding execution with universal Mersenne-disjoint return sets | One check on C1; zero checks on the avoiding execution |
| `lem:no-proper-core`, node `[8]` | Target-avoiding lexicographically minimal packed context and one explicit proper-subgraph certificate | CT2 certified-reduction profile through `Graph.PackedMinimumDegreeCycle` | Every proper subgraph has minimum degree at most two; exact deletion-C2 terminal and trace; totality and semantic contradiction | One local certificate check; degree-zero polynomial budget |
| `lem:deletion-critical`, nodes `[9]`, `[10]`, `[67]` | The fixed-vertex view of the same packed minimal context and its exact CT1 avoiding output | Registered CT1-to-local-deletion CT2 route | Exact disabled dart discovery, a degree-three endpoint on every edge, and independence of degree-at-least-four vertices | At most one scan of the declared dart list; each explicit deletion-C2 branch has one local check |
| `def:boundaried-gluing` through `cor:uncompressible`, nodes `[11]`–`[14]` (also reused at `[36]`–`[39]`) | `VerifiedNoProperCorePrefix` on the same packed minimal context | Literal `Graph.PackedBoundariedGluing` semantics plus the CT3 certified-reduction kernel | Exact vertex and edge arithmetic for gluing; local-to-global lexicographic decrease; degree preservation at atom, context, and boundary vertices; target and baseline transport through a reconstruction isomorphism; replacement contradiction and hereditary target-uncompressibility for normalized decompositions with nonempty boundary; composed `VerifiedBoundariedReplacementPrefix` | Proof-level construction only: one certified reduction, no enumeration of contexts, graphs, subgraphs, or replacements |
| `thm:p13free`, `cor:p13-exists`, nodes `[15]`–`[16]` | `VerifiedBoundariedReplacementPrefix` and target avoidance on the identical packed minimal context | CT1 target-certificate profile through `Graph.InducedPath.Profile`; HSS is the sole trusted external closure | Literal `P₁₃`-free avoiding terminal and trace; HSS contradiction; induced `P₁₃` realization; exact C1 terminal and trace; totality; composed `VerifiedInducedP13Prefix` retaining all preceding outputs | Zero checks on the proof-carrying avoiding run; one check on a supplied Mathlib induced embedding; degree-zero polynomial budgets; no tuple, path, subgraph, or graph universe is enumerated |
| `sec:remainder`, node `[17]` and the packing-derived clauses of `[25]`–`[27]` | `VerifiedInducedP13Prefix` on the identical selected packed graph | Registered `CT1.terminal.c1->CT12` route plus the CT12 disjoint-packing profile through `Graph.InducedPathPacking` | The route preserves the branch context, materializes exactly the selected-list CT12 input, and derives its nonemptiness from the CT1 realization; a maximum vertex-disjoint induced-`P₁₃` family; maximal saturation; exact exhausted CT12 run with `p₁₃` iterations; `13 p₁₃ ≤ n`; `|R| + 13 p₁₃ = n`; `R` and every induced subgraph of `R` are `P₁₃`-free; HSS rules out every finite internal subgraph of minimum degree at least three; composed `VerifiedP13PackingPrefix` retaining every prior stage | CT12 visits exactly the selected packing list, once per packed window and hence at most `n` iterations; trace length at most `4n + 3`; the embedding and packing universes are not materialized |
| `lem:labels` and the definitions of `C_s` and `Ω₂`, node `[18]` | `VerifiedP13PackingPrefix` on the identical selected packed graph | CT10 exact accepted-class profile through `CT10.ExhaustiveClassification` and `Graph.InducedPathAttachment` | Exact legality equivalence; `8192` compact candidates; `399` legal labels; size distribution `13,60,122,122,63,17,2`; legal sizes `1`–`7`; exhaustive terminal, exact typed trace, semantic validity and totality; exact `C_s` and `Ω₂`; every actual attachment accepted; composed `VerifiedP13LabelAlgebraPrefix` retaining the exact CT12 predecessor | `167792 = 8192 + 399 + 399²` primitive candidate/direct/row checks, bounded quadratically in the explicit candidate universe; no graph, path, subgraph, or context universe is enumerated |
| `lem:sparse-upper-envelope`, `lem:sparse-slack-surplus`, node `[126]` | `VerifiedSparseSurplusPrefix` at node `[125]`, retaining the selected packed context, CT2 no-proper-core theorem, deletion criticality, and the exact CT6 degree-excess ledger | `Graph.DegeneracyPeeling.Profile` with the exact CT12 list-peeling runner | Actual cubic root; literal complement; induced-core freeness; exhausted terminal; exact typed trace; validity and totality; exactly `n-1` iterations; `e(G-v)≤2(n-1)-3`; `m≤2n-2`; `σ=2m-3n=n-6-2λ`; exact equality with the existing CT6 degree-excess ledger; composed `VerifiedSparseEnvelopePrefix` | Linear CT12 schedule on one proof-selected list. The sharp edge proof recurses only on a strictly smaller explicit support; no graph, subgraph, order, path, or context universe is enumerated |
| `lem:sparse-excess-port-extraction`, cubic-endpoint clause of `lem:sparse-port-activation`, nodes `[127]`–`[128]` | `VerifiedP13LabelAlgebraPrefix` and deletion criticality on the identical selected packed graph | CT6 ordered activity profile through `Graph.SurplusPortActivity` | Exact active-ledger terminal and trace; first-failure semantics for the first high centre with a non-cubic neighbour; deletion-critical exclusion of every failure; exact `Σ_v(d(v)-3)` ledger; excess-slot cardinality; composed `VerifiedSparseSurplusPrefix` | One failure test per declared vertex and at most `|V|²` primitive adjacency/degree tests; no enumeration of paths, subgraphs, graphs, or attachment tables |
| Remaining clauses of `lem:sparse-port-activation`, nodes `[127]`--`[128]` | `VerifiedSparseEnvelopePrefix`, CT2 bridgelessness, and the actual CT6 active ledger on the identical graph | `Graph.SurplusPortActivation` with open suppression and triangular return profiles | One activated demand for every CT6 slot; exact root return; open or triangular response; exact `T(p)`, `Γ(p)` edge/vertex supports; activated schedule length equal to the CT6 residual and to `σ(G)`; composed `VerifiedSurplusPortActivationPrefix` | One local certificate per supplied slot; schedule-linear outer scan; no path-family, cycle-family, subgraph, graph, or pair-universe enumeration |
| `rem:ct9-surplus-slot-stratification`, pair-availability precursor to node `[130]` | The actual CT6 active-ledger residual in `VerifiedSparseSurplusPrefix` | Registered `CT6.residual.activeLedger->CT9` route and graph-owned capacity-one surplus-slot profile | Exact item count `σ(G)`; context and route provenance; verified total CT9 execution; bounded branch `σ(G) ≤ 1` or overload branch with two distinct slots; composed `VerifiedSurplusPairPrefix` | One partition scan of exactly `σ(G)` supplied slots; no pair, path, subgraph, graph, or response-table enumeration |
| `lem:heavy-neighbourhood-normal-form`, `def:surplus-ports`, `def:heavy-center-triangular-port` | `VerifiedSurplusPairPrefix`, target avoidance, and deletion criticality | CT1 four-cycle target profile plus CT10 selected-port classification in `Graph.HighCenterStructure` and `Graph.SurplusPortActivity` | Exact avoiding terminal for length four; matching/common-neighbour consequences; canonical port endpoints and two shoulders; exhaustive open/triangular state split; composed `VerifiedSurplusPortClassificationPrefix` | Zero CT1 realization checks on the proof-carrying avoiding run; CT10 work at most `2|V|²+2` |
| Same-centre open-port precursor to `lem:same-center-open-port-compatibility` | `VerifiedSurplusPortClassificationPrefix` | CT9 capacity-one centre fibres in `Graph.SurplusPortActivity` | Either a same-centre pair of distinct open selected slots or at most one such slot at every centre; composed `VerifiedOpenPortPairPrefix` | At most `|V|³+|V|` primitive label/item checks; pairs are not enumerated |
| Exact local-response precursor to the compatible-pair branch | An actual CT9 open-centre overload residual | Registered `CT9.residual.overload->CT7` route plus `Graph.AdjacencyResponse` | Bounded CT9 branch retained; overload maps its exact pair to canonical endpoints and yields the first adjacency-response distinction or complete response neutrality; composed `VerifiedOpenPortResponsePrefix` | Two linear CT7 passes, at most `2|V|+1` checks; no completion graphs or response tables are materialized |
| Shoulder-pair clause of `def:surplus-ports` and local shoulder bookkeeping | `VerifiedOpenPortResponsePrefix` and deletion criticality | CT5 local witness ledger in `Graph.PortShoulderLedger` | Every selected port has an exact two-shoulder witness; exact charge terminal and trace; ledger total `2|P_slot|`; composed `VerifiedPortShoulderLedgerPrefix` | One singleton-witness check and one ledger contribution per slot, bounded by `2|V|²+2` |
| `def:fan-compatible-open-ports`, `lem:same-center-open-port-compatibility`, node `[69]` | `VerifiedPortShoulderLedgerPrefix`, the exact CT9 overload pair routed through CT7, and four-cycle avoidance | CT7 semantic interpretation in `Graph.OpenPortCompatibility` | Bounded centre fibres retained; overload endpoints are adjacent or the exact shoulder nonincidence/disjointness predicate holds; composed `VerifiedOpenPortCompatibilityPrefix` | Proof-level interpretation after the existing `2|V|+1` CT7 bound; no additional finite enumeration |
| `lem:heavy-center-triangular-alternative`, `cor:heavy-center-local-dichotomy`, numerical clause of `cor:degree-four-local-activation`, node `[69]` | `VerifiedOpenPortCompatibilityPrefix`, deletion criticality, and four-cycle avoidance | CT10 all-incident-port profile in `Graph.HighCenterPort` | Exact open/triangular partition of all ports at each high centre; compatible open pair or at least `d(h)-2` triangular ports; composed `VerifiedHighCenterPortDichotomyPrefix` | At most `2d(h)+2 ≤ 2|V|+2` checks for a requested centre; port pairs are not enumerated |
| `def:triangular-fan-core`, `lem:triangular-shoulder-completion`, node `[78]` | `VerifiedHighCenterPortDichotomyPrefix`, minimum degree three, deletion criticality, and four-cycle avoidance | CT5 dependent shoulder-witness profile in `Graph.TriangularShoulderCompletion` | A completion incidence at every triangular shoulder; at most one central shoulder; central cubicity and unique central completion; no noncentral centre-neighbour completion endpoint; composed `VerifiedTriangularShoulderCompletionPrefix` | At most `2|V|²+2|V|+2` checks per requested centre; no paths, subsets, pairs, or graphs are enumerated |
| `lem:bridgeless` | `VerifiedTriangularShoulderCompletionPrefix` on the same minimum-degree-three packed minimal context | CT2 certified reduction through `Graph.BridgeContraction` and `Graph.PackedBridgeReduction` | Literal bridge contraction; one fewer vertex; preserved minimum degree; every contracted cycle lifts to a source cycle with identical length; every dart is non-bridging; composed `VerifiedBridgeReductionPrefix` | One certificate check only on the contradictory bridge branch; no graph, component, path, cycle, subset, or replacement universe is enumerated |
| `lem:triangular-port-return`, node `[79]` | `VerifiedBridgeReductionPrefix`, one actual triangular port, and target avoidance | Framework-native CT2-to-return transition followed by the CT1 target-certificate profile in `Graph.TriangularPortReturn` | Simple shoulder-to-centre path omitting the port endpoint; restored simple cycle of exact length `|Q|+2`; exclusion `|Q| ≠ 2^j-2`; exact four-way initial landing split; composed `VerifiedTriangularPortReturnPrefix` | One supplied-certificate CT1 check; reachability-to-path is proof-level choice; no walk, path, cycle, subset, subgraph, or graph universe is enumerated |
| `lem:triangular-first-landing`, node `[80]` | `VerifiedTriangularPortReturnPrefix` and the exact CT5 completion-incidence predicates on the identical selected graph | CT10 three-class profile and framework theorem composition in `Graph.TriangularFirstLanding` | Every actual completion incidence is central, cross-triangular, or outside; port vertices and other centre neighbours are excluded; the first noncentral completion of the verified CT1 return carries the computed class; composed `VerifiedTriangularFirstLandingPrefix` | At most `6|V|²+3` checks on the explicit shoulder-site × vertex table; no path, subgraph, graph, or context universe is enumerated |
| `lem:triangular-cross-shoulder`, node `[81]` | `VerifiedTriangularFirstLandingPrefix`, two distinct triangular ports, and four-cycle avoidance | CT9 capacity-one fibre in `Graph.TriangularCrossShoulder` | Distinct port endpoints are nonadjacent and their shoulder pairs are disjoint; two cross edges force a high shoulder or a four-cycle; exact high-shoulder/bounded state split; cubic shoulders force the typed bounded run; composed `VerifiedTriangularCrossShoulderPrefix` | At most five checks on the four explicit shoulder pairs and one unit label; no pair set, path, subgraph, or graph universe is enumerated |
| `def:typeB-window-incidence-profile`, `def:fan-closed-port`, `lem:compatible-pair-fan-closure`, node `[72]` | `VerifiedTriangularCrossShoulderPrefix`, the literal `P₁₃` window/remainder partition, two distinct fan-compatible open ports, and four assigned local incidences | CT5 exact four-site ledger in `Graph.FanClosedPort` | Window/non-window incidence kinds and three support types are computed; both port vertices are remainder-side and both ports are derived fan-closed; the four oriented carriers are pairwise distinct; exact charge terminal/trace, totality, and composed `VerifiedFanClosedPortPrefix` | Exactly ten checks on four sites with one `Unit` witness each; no vertex, pair, path, subgraph, graph, or assignment universe is enumerated |
| Local count/deficit clauses of `prop:fan-closed-port-typeB-routing` and `cor:compatible-pair-typeB-routing`, node `[72]` | `VerifiedFanClosedPortPrefix` and its actual CT5 charge residual | Registered `CT5.residual.chargeLedger->CT14` route plus `Graph.FanClosedPortMass` | CT14 scans the literal cubic-closed-neighbour subtype; its lower mass and unit-label multiplicity equal the subtype cardinality; the two compatible ports inject into it; the quarter-deficit numerator is at least `k-3 > 0`; exact capacity terminal/trace, route provenance, totality, and composed `VerifiedFanClosedMassPrefix` | At most `4|V|²+4|V|+1` primitive predicate/member checks; the subtype list has linear size and no subsets, assignments, paths, subgraphs, or graphs are enumerated |
| `def:typeB-hybrid-incidence`, `lem:typeB-hybrid-incidence-budget`, and the local part of `lem:typeB-hybrid-B1`, node `[72]` | `VerifiedFanClosedMassPrefix`, target-derived four-cycle avoidance, and the explicit marked-fan branch input `d(h) ≤ 8` | Registered `CT14.residual.capacity->CT14` route plus `Graph.HybridFanIncidence` | Exactly two literal non-centre incidences per actual cubic-closed member; pairwise-distinct non-centre endpoints; exact window/non-window multiplicity partition; total credit `4c`; deficit slack `4c-(4c+k-11) ≥ 3`; non-window credit pays the demand left after window credit; exact capacity terminal/trace, route provenance, totality, and composed `VerifiedHybridFanIncidencePrefix` | At most `4|V|²+20|V|+1` primitive checks; the stored incidence list has exactly `2c ≤ 2|V|` entries and no closed-member×vertex table, subsets, assignments, paths, subgraphs, or graphs are enumerated |
| `def:closed-fan-window-pair`, `def:direct-cycle-free-closed-pair`, and `lem:typeB-direct-fan-window-cycles`, node `[72]` | `VerifiedHybridFanIncidencePrefix` and target avoidance on the same selected graph | Certificate-driven CT1 through `Graph.FanWindowCycle`, using `Graph.InducedPathBridge` | Exact arithmetic violation type; equivalence with the five direct-safety clauses; literal internal-attachment, centre-crossing, and interlacing simple-cycle constructors; exact avoiding terminal/trace/totality; all closed pairs direct-cycle-free; composed `VerifiedDirectFanWindowPrefix` | Zero checks on the avoiding run and one check on a positive certificate; path segments are symbolic and no label, walk, path, tuple, subset, subgraph, or graph universe is enumerated |
| `lem:typeB-two-window-cycles`, node `[72]` | `VerifiedDirectFanWindowPrefix`, two literal vertex-disjoint induced windows, and target avoidance | Certificate-driven CT1 through `Graph.TwoWindowCycle` and the orientation-independent bridge in `Graph.InducedPathBridge` | Literal two-window simple cycle of exact length `4+|i-j|+|a-b|`; exact avoiding terminal/trace/totality; every two-window datum target-safe; composed `VerifiedTwoWindowCyclePrefix` | Zero checks on the avoiding run and one check on a positive certificate; no position pair, label, walk, path, tuple, subset, subgraph, or graph universe is enumerated |
| Degree-cap clause of `lem:fan-certificate`, node `[70]` | `VerifiedTwoWindowCyclePrefix` and one certificate-marked fan contract on the same graph | CT9 capacity-one representative slots through `Graph.P13FanLabelPacking` | Exact bounded terminal and trace; injective representative-slot labelling; every certificate-marked fan has `d(h) ≤ 8`; composed `VerifiedFanLabelPackingPrefix` | Eight label fibres over exactly `d(h)` incident ports. The fixed 13-position arithmetic certificate is compiled separately; no attachment-code or label-family universe is enumerated |
| Non-singleton clause of `lem:fan-certificate`, node `[70]` | `VerifiedFanLabelPackingPrefix`, one actual fan port, and two distinct positions in its marked label | Second CT9 bounded partition through `Graph.P13MarkedFanLabelPacking` | Two zero-capacity blocked slots, six capacity-one slots, at most six other labels, and exact bound `d(h) ≤ 7`; composed `VerifiedMarkedFanLabelPackingPrefix` | Eight fibres over the erased actual port list. A cached `13³=2197` position certificate and `8²=64` capacity identity; no attachment-code or label-family universe is enumerated |
| Certificate-closed charge clause of `lem:fan-certificate`, node `[70]` | `VerifiedMarkedFanLabelPackingPrefix`, the literal assigned-incidence relation on actual fan ports, and the defining inequality `4c+k≤11` | `Graph.AssignedFanCharge` plus CT14 aggregate mass through `Graph.CertificateClosedFanCharge` | Cubic closure iff both non-center incidences are assigned; exact internal-degree quarter charge; derived `-1` closed and `≥3` open bounds; exact closed count `c`, open count `k-c`, capacity terminal/trace, coarse charge identity `11-k-4c`, and nonnegative closed-neighbourhood lower bound; composed `VerifiedCertificateClosedFanChargePrefix` | A constant number of passes over exactly `k=d(h)` ports; no fan subset, closure assignment, label family, path, subgraph, or graph universe is enumerated |
| `prop:fan-closed-port-typeB-routing`, `lem:typeB-multiclosed-budget`, and `lem:typeB-hybrid-incidence-budget`, node `[72]` | `VerifiedCertificateClosedFanChargePrefix`, one actual marked fan, its decidable assigned-incidence predicate, and two actual assigned compatible fan-closed ports | Existing graph-owned CT5-to-CT14 mass stage and registered CT14-to-CT14 hybrid-incidence refinement | The marked-fan CT9 result derives `k≤8`; the two ports derive `c≥2`; hence `4c+k-11>0`; the exact endpoint-disjoint hybrid ledger pays the deficit with slack at least three; composed `VerifiedPositiveDeficitFanEntryPrefix` | At most `4|V|²+20|V|+1` primitive checks over the actual cubic-closed subtype and exactly two incidences per member; no port subsets, label families, candidate ledgers, paths, subgraphs, contexts, or graphs are enumerated |
| `lem:typeB-hybrid-B1` and `cor:typeB-local-entry-is-B1`, node `[72]` | `VerifiedPositiveDeficitFanEntryPrefix` with its exact CT14 execution | Framework-owned semantic projection `Graph.HybridFanIncidence.LocalLedgerEntry` | Exact `2c` incidence count, endpoint-disjointness, window/non-window partition, total deficit payment, non-window remaining-demand payment, and composed `VerifiedLocalB1Prefix` | Projection only after the existing CT14 run; no new scan or finite universe |
| Positive-deficit branch of `def:typeB-candidate-ledger`, nodes `[72]`--`[73]` | `VerifiedLocalB1Prefix`, its literal hybrid-incidence universe, and an ordinary-reserve predicate on those carriers | Core `FiniteWeightedSelection` and `Graph.HybridFanCandidate` | Exact candidate subtype: all window incidences selected, no reserve-used incidence selected, and exact non-window payment; finite candidate fibre; constructive all-incidence candidate under local reserve-freeness; composed `VerifiedPositiveDeficitCandidatePrefix` | The witness scans exactly `2c` incidences. Finiteness is proof-level; no powerset, candidate product, demand subset, path, subgraph, context, or graph universe is evaluated |
| Certificate-closed branch of `def:typeB-candidate-ledger`, nodes `[72]`--`[73]` | `VerifiedPositiveDeficitCandidatePrefix`, one certificate-closed marked fan, its actual port list, and an ordinary-reserve predicate on vertex carriers | Core `FiniteWeightedSelection`, `Graph.AssignedFanCharge`, and `Graph.CertificateClosedFanCandidate` | Exact candidate subtype with assigned-degree quarter weight `11-4(1+a)`, derived closed weight `-1` and open lower bound `3`, nonnegative center-plus-selected-neighbour charge, reserve exclusion, literal adjacency, deletion-critical degree three and exclusion from `H_X`; constructive complete-neighbour candidate under local reserve-freeness; composed `VerifiedTypeBCandidateFibresPrefix` | The witness scans exactly `k` ports. Finiteness is proof-level; no powerset, candidate product, demand subset, path, subgraph, context, or graph universe is evaluated |
| Dependent family in `def:typeB-candidate-ledger`, node `[73]` | A literal finite declared center set, one verified certificate/positive local branch per center, and the ordinary reserve | Core `DependentWeightedSelection` and `FiniteRefinedLedger`, plus `Graph.RefinedFanLedger` | Heterogeneous literal item family; candidates, finiteness, selected support, and declared overlap support are derived; every center remains visible even when its valid fibre is empty; demand count at most `|V(G)|`; composed `VerifiedTypeBDemandSystemPrefix` | Linear schedule and local item-support scans; no candidate product, demand powerset, path, subgraph, context, or graph universe is evaluated |
| Disjoint-family clause of `lem:typeB-maximal-completion` and `lem:typeB-bridge-to-overlap`, node `[73]` | `VerifiedTypeBDemandSystemPrefix` on the complete declared schedule | Core `FiniteRefinedLedger` and CT12 `RefinedLedgerCompletion` | Unconditional empty/nonempty full-choice-or-obstruction theorem; least-cardinality nonempty obstruction with choices on every proper shorter nonempty subschedule; exhausted CT12 run and at most `|V(G)|` iterations; composed `VerifiedTypeBCompletionPrefix` | One peeling iteration per demand. Choice and `Nat.find` minimality are proof-level; no candidate product or demand subset is materialized |
| Exact support and unconditional clauses of `def:typeB-overlap-obstruction` and `lem:typeB-global-local-reflection`, node `[73]` | Failure of the full dependent choice | Derived declared carrier universes plus target avoidance and deletion criticality | Proof-carrying minimal obstruction; reserve-blocked centers retained; every demand center in support; ambient dyadic safety; independent high centers; cubic center neighbors; proper-subfamily choices; composed `VerifiedTypeBOverlapSupportPrefix` | Linear declared-support union; proof-level obstruction selection, no subfamily enumeration |
| Ordinary high-center completeness split in `def:typeB-bridge-statements`, nodes `[73]`--`[74]` | A literal vertex support and ordinary reserve, with no supplied center list or entry-completeness assertion | Core `FiniteResolution` followed by the derived dependent CT12 family | All support vertices of ambient degree at least four are derived as sites; exact alternative between one literal center with no verified local entry, a full disjoint choice, or a minimal overlap obstruction; composed `VerifiedTypeBResolutionPrefix` | Linear high-center filter; witness-family resolution and CT12 choice are proof-level and enumerate no dependent products |
| `def:typeB-assigned-ledger`, `def:typeB-candidate-ledger`, `lem:typeB-exact-postledger`, `lem:typeB-postledger-core-hygiene`, `def:typeB-center-deleted-overload`, `prop:typeB-unconditional-deficit`, and `prop:typeB-bridge-reduction`, nodes `[73]`--`[74]` | `VerifiedTypeBResolutionPrefix`, retained through `VerifiedTypeBChoiceLedgerPrefix` and `VerifiedTypeBAssignedChargePrefix` on the identical minimal context | The already executed CT14 fan-mass and hybrid-incidence profiles, the CT12 full choice, and reusable `Graph.AssignedSupportCharge`, `Core.FiniteReceiverDischarge`, `Core.FiniteBoundaryTransfer`, `Graph.FiniteInducedBoundary`, and `Graph.HighCenterDeletionCharge`; no new route | Exact no-double-counted post-ledger split; on a full choice, net nonnegativity, a saturated receiver, or strict boundary overload with a literal landing and `-net ≤ 800 * assignedSurplus`; without any local-choice hypothesis, `-net ≤ 21 * assignedSurplus + receiverOverload`; composed `VerifiedTypeBPostLedgerPrefix` and public `exists_verifiedTypeBPostLedgerPrefix` | CT12 uses at most `|V|` iterations and the inherited CT14 incidence audit is at most `4|V|²+20|V|+1`; the new graph transition consists of finset filters, images, unions, cuts, and sums, while receiver and transfer witnesses are proof-selected and no function, subset, path, subgraph, context, or graph universe is enumerated |
| `def:sparse-canonical-connector`, `def:surplus-blockers`, `def:sparse-pair-response`, and `lem:sparse-pair-dependence-exit`, nodes `[130]`, `[132]` | `VerifiedBaselineSpineDemandPrefix`, retaining the exact activated CT6 slot schedule from nodes `[127]`--`[128]` on the identical selected graph | Core `FiniteBlockerLedger.FamilyProfile`, `Graph.FiniteConnector`, `Graph.FiniteSupportResponse`, `CT15.AdmissibleQuotient`, and `Graph.SurplusPairResponse` | Every unordered slot pair occurs once; exact disjoint free/blocked partition; first local blocker retained; both exact `Γ` supports and one minimum-distance connector retained for every free pair; raw boundary/target mismatch audit separated from admission; every admitted non-injective quotient yields a certified smaller counterexample and is impossible by minimality; exact CT15 full-rank terminal, trace, validity, totality, and composed `VerifiedSparsePairResponsePrefix` | Pair schedule at most `n^4`; every blocker scan is over the two supplied local supports, returns, fixed role list, and retained cycles; each connector verifies one retained shortest path; no graph, subgraph, path family, quotient proposal family, or context universe is enumerated |
| Five-role pre-retokenization dispatch in `def:total-surplus-pair-token-route` and the free-anchor clause of `lem:total-pair-token-route-no-overcount`, node `[131]` | `VerifiedSparsePairResponsePrefix` and its exact pair schedule, free subtype, blocked subtype, connectors, canonical first blockers, and the node-`[126]` sparse-envelope bound | `CT9.TokenRoleLedger`, `Graph.SurplusTokenRole`, and `Graph.SurplusPairTokenRouting` | Exact CT9 execution with exhaustive terminal, semantic validity, valid trace, and totality; exact initial selected-port×role partition; five exact dispatch roles; `freeAnchor` iff the blocker scan is negative; free fibre token equals the first selected port; retained connector support transported; canonical blocker first-hit proof transported; composed `VerifiedAllPairTokenRoutingPrefix` | The sparse residual has at most `n` selected-port tokens and hence at most `n²` pairs; the complete five-role scan has the verified bound `5n³`; no Boolean-state, graph, context, path-family, or recursive enumeration |
| `lem:sparse-pair-dependence-exit`, `def:capacity-token-ledger`, `lem:exact-window-join-identity`, and `lem:total-pair-token-route-no-overcount`, nodes `[133]`--`[136]` | Green `VerifiedAllPairTokenRoutingPrefix`, including the unchanged complete pair list, the blocked canonical first hit, and the free-anchor token | `Graph.InducedPathWindowLedger`, `Graph.SurplusCapacityTokenRouting`, and the reusable CT9 product ledger | Raw audit exits impossible on admitted candidates; total blocked token priority; exact `15p₁₃+σ_W` window supply; exact three-class token sum; exact 25-role complete-pair partition; composed `VerifiedCapacityTokenPrefix` | Window audit at most `13n²`; complete pair×token×role audit at most `225n³`; no graph, path, matching, Boolean-state, or context universe |
| `prop:exact-25-role-coupled-decision`, nodes `[137]`--`[139]`, `[141]` | Green `VerifiedCapacityTokenPrefix`, hence the exact pair list and its total token/role map on the identical selected graph | Generic `CT9.ClasswiseTokenLedger` and `Graph.SurplusClasswiseOverload` | Exact capacity decision; positive branch with an actual overloaded fibre; literal constructor route to window, remainder, or primitive; negative branch `σ²≤(450bmax+1)n`; composed `VerifiedCoupledClassOverloadPrefix` | At most `225n³` comparisons on the existing finite lists; no matchings, stars, graphs, paths, state cubes, or recursion are generated |
| `def:near-cubic-spine`, node `[19]` | Green `VerifiedP13LabelAlgebraPrefix` on the same selected graph | Core `QuadraticScaleSplit` with the explicit downstream homogeneous-cap coefficient | Exact exhaustive comparison `C n < σ² ∨ σ² ≤ C n`; composed `VerifiedSurplusScaleSplitPrefix` | One natural-number comparison; no square root, floating point, graph family, or threshold search |
| `def:deficiency-surplus`, node `[28]` | Green `VerifiedP13PackingPrefix` and its exact selected remainder from nodes `[25]`--`[27]` | Reusable `Graph.AssignedSupportCharge.Profile` | Literal induced-remainder degree and exact sum `def⁺(R)=Σ_v∈R (3-d_R(v))`; retained no-internal-three-core certificate; composed `VerifiedP13PositiveDeficiencyPrefix` | One finite neighbour scan per remainder vertex; no subgraph or support-family enumeration |
| `lem:stub-positive`, `lem:surplus-aware-window-stub`, `lem:wedge-lower`, `def:curvature-target-rank`, and `lem:target-rank-circuit`, nodes `[29]`--`[35]` | Green `VerifiedP13PositiveDeficiencyPrefix` on the exact node-`[28]` remainder | Reusable `Graph.PositiveDeficiencyWedge`, `Graph.InducedPathWindowLedger`, `Graph.FiniteSupportResponse`, and `CT15.AdmissibleQuotient` | Exact `def⁺(R)≤e(R,W)≤15p₁₃+σ_W`; exact surplus-adjusted inequality after subtracting `σ_R`; exact wedge floor `W₂(R)≥3|R|-2def⁺(R)`; literal raw wedge coordinates with cardinality `W₂(R)` and the proved bound `W₂(R)≤n³`; exact CT15 full-rank terminal and trace; every admitted noninjective quotient is impossible by certified reduction and minimality; composed `VerifiedP13CurvaturePrefix` | Quadratic neighbour-incidence accounting plus one linear scan of at most `n³` actual wedge coordinates; no support, quotient, context, path, subgraph, or graph family is enumerated |
| `lem:curvature-dependence-routing` and `lem:proper-smearing`, nodes `[40]`--`[42]` | Green curvature rank-drop routing interface from nodes `[36]`--`[39]`, on the identical selected context | Framework-owned `Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization` and the existing CT3 compression kernel | A proper enlargement carries an injective graph embedding fixing every boundary vertex, strict packed-rank growth, and an exact quotient realization; the node-`[39]` enlarged constructor has literally the `proper | whole` type consumed at node `[40]`; the combined route retains earlier context defects and executes the proper-support audit without an implicit handoff; a proper support returns an actual distinguishing context or its universal side executes the certified CT3 contradiction; the whole payload is retained unchanged for node `[43]`; composed `VerifiedP13ProperDelocalizationPrefix` | One proof-supplied context-universality audit and constant CT3 execution; no contexts, supports, quotients, subgraphs, or graphs are generated |
| `lem:smearing-support-repair`, repaired `lem:no-silent-global-smearing`, and the admissible-rank join, nodes `[43]`--`[47]` | Green proper/whole payload from nodes `[40]`--`[42]` | `CT15.AdmissibleQuotient`, `Graph.ClosedRankDrop`, and `Graph.OneThreeRepair` | The whole payload carries the admitted finite quotient and its literal distinct-coordinate identification; the quotient's certified-reduction field and minimality derive injectivity, closing node `[46]`; exact graph-computed identity `s=p-2+2β-σ`; unconditional full-rank join at node `[47]`; composed `VerifiedP13GlobalRankClosurePrefix` | One constant logical admission check and linear finite graph degree sums; no quotient family, context family, representative family, or graph universe is generated |
| Degree-four local profile and assigned marking, nodes `[78]`--`[80]` | Green `VerifiedFanLabelPackingPrefix` and the actual high-center schedule | `Graph.DegreeFourFanLedger` and `Graph.FiniteCertificateMarking` | Exact higher-center/no-higher split; on the latter branch `d(h)=4`, exact local CT14 ledger, and exhaustive assigned-certificate/residual split; composed `VerifiedDegreeFourTypeBLedgerPrefix` | At most `23(n+1)²` primitive checks over actual centers |
| Exact local-entry and B2 exhaustion, nodes `[81]`--`[83]` | Green node-`[80]` assigned certificate for every center | Core `FiniteResolution`, CT12 refined-ledger completion, and graph post-ledger charge decomposition | Every resolved entry proves equality with the node-`[80]` certificate; exhaustive unresolved/nonnegative/remaining-negative/minimal-overlap route; minimal obstruction retains all proper-subschedule choices; composed `VerifiedDegreeFourB2RoutingPrefix` | Linear center resolution and one CT12 peel per demand; no dependent-choice product or demand powerset is evaluated |
| Ordinary Type B residual-center payment, node `[75]` | Green degree-four B2 route on the same `TypeBSupportScope` | Reusable `Graph.HighCenterDeletionCharge` assigned-surplus ledger | Certificate failures, unresolved entries, and every selected minimal-overlap center are literal high centers; their finite count is bounded by the exact assigned surplus; composed `VerifiedTypeBResidualCenterLedgerPrefix` | Finite-set and subschedule cardinality only; no envelope or support family is generated |
| `lem:same-token-matching-star`, nodes `[140]`, `[142]`, `[143]` | Green actual overloaded token--role fibre and its exact node-`[139]`/`[141]` constructor route | Core `GreedyMatchingStar` and graph `SurplusHomogeneousPattern` | Deterministic maximal matching, exact coverage, sharp `(L-1)(2L-3)` cap, and a literal matching-or-star certificate at the routed class threshold; composed `VerifiedHomogeneousPatternPrefix` | At most `3m²` pair-intersection/incidence checks on the supplied fibre; no matching, star, pair, graph, or path family is generated |

The next green-input frontiers are node `[144]` on the Part X
matching--star branch and node `[84]` on the degree-four residual fan-mass
branch. Node `[21]` remains downstream of the node-`[19]` scale split.

## Node `[79]`: certificate-driven triangular-port return

`Graph.DartReturn.ofNotBridge` converts the CT2 non-bridge theorem into one
simple path in the graph with the root edge deleted. It invokes Mathlib's
`Reachable.exists_isPath` theorem and selects its proved witness; it contains
no path enumerator. `Graph.PackedMinimumDegreeCycle.
BridgeReductionStage.dartReturn` is the reusable transition from the
framework-owned CT2 stage.

`Graph.TriangularPortReturn` proves that the first return vertex is one of the
two declared shoulders, removes that first edge, and obtains a simple
shoulder-to-centre path whose support omits the port endpoint. Restoring the
two removed edges gives a simple cycle of exact length `|Q|+2`. Target
avoidance excludes that length, and the Erdős adapter derives
`|Q| ≠ 2^j-2` for every `j ≥ 2`.

The graph theorem records four exact initial alternatives: a one-edge central
return; an immediate noncentral completion; the two-edge
shoulder-then-central return; or a shoulder edge followed by a noncentral
completion at the other shoulder.

The CT1 code is the proof-carrying return itself. The runner validates that
one certificate, reaches C1, and reports exactly one check. The independent
`EvenCycleExample.TriangularPortReturnTransfer` namespace instantiates the
same profile for an arbitrary cycle-length predicate.

## Nodes `[5]`–`[7]`: edge-rooted Mersenne CT1

### Reusable graph layer

`StructuralExhaustion.Graph.EdgeRootedReturn` packages:

- an oriented Mathlib dart `e = uv`;
- a walk from `v` to `u` in the graph with `e` deleted;
- a simple-path proof; and
- the selected predicate on the return length.

The graph layer proves:

- `EdgeRootedReturn.ofCycle`;
- `EdgeRootedReturn.cycle` and `cycle_isCycle`;
- `hasCycleWithLength_iff_hasEdgeRootedReturn`;
- `hasEdgeRootedReturn_iff_exists_mem_returnSet`; and
- `noCycleWithLength_iff_returnSets_disjoint`.

`Graph.MinimumDegreeCycleRouted` supplies the target certificate encoding,
positive and avoiding CT1 runners, exact return-set consequence, registered
local-deletion route, and fixed-vertex prefix.

### Erdős arithmetic and execution

`Erdos64EG.Internal.TargetAlgebra` defines:

- `MersenneLength r := PowerOfTwoLength (r + 1)`;
- `MersenneSet` and the manuscript return set;
- `mersenneLength_iff`;
- `hasPowerCycle_iff_hasRootedReturn`;
- `target_iff_hasMersenneReturn`; and
- `not_target_iff_returnSets_disjoint`.

`runMersenneCT1` and `runCT1` reach `c1Terminal` with trace

```text
entry → equivalenceCertification → realizationDecision → c1Terminal
```

and check count one. `runAvoidingCT1` reaches `avoidingTerminal` with the same
prefix and check count zero. `runAvoidingCT1_returnSets_disjoint` extracts the
universal Mersenne-disjointness theorem from that execution.

The `K₄` fixture constructs the four-cycle, its length-three rooted return,
and the exact C1 terminal, trace, and check count.

## Node `[8]`: no proper core

### Packed finite graphs and manuscript rank

`StructuralExhaustion.Graph.PackedFiniteObject` hides the finite graph's
vertex type inside the ambient object. Its rank is

```text
vertexCount ^ 3 + edgeCount.
```

The graph layer proves that a simple graph has at most `vertexCount ^ 2`
edges. Consequently:

- fewer vertices always give a smaller rank; and
- at equal vertex count, fewer edges give a smaller rank.

Thus `Core.AvoidingContext.exists_minimalCounterexample` selects the
manuscript's lexicographic minimum by proof-level `Nat.find`. It does not
enumerate finite graphs.

`PackedFiniteObject.ProperSubgraph G` contains exactly the local mathematical
data needed for a proper subgraph:

- a finite graph `H`;
- an embedding of `V(H)` into `V(G)`;
- inclusion of the mapped edge relation in `G`; and
- strict lexicographic decrease, either in vertex count or, at equal vertex
  count, in edge count.

`CycleWithLength.mapHom` and
`ProperSubgraph.hasCycleWithLength_mono` transport an accepted simple cycle in
`H` through the injective Mathlib graph homomorphism, preserving its exact
walk length.

### CT2 execution

`CT2.CertifiedReductionInput` receives the proof-carrying smaller object, its
baseline, and target transport. `CT2.runCertifiedReduction` constructs the
canonical deletion-C2 execution:

```text
entry → deletionDecision → deletionC2Terminal
```

The framework proves its typed path, semantic contradiction, totality, check
count one, and constant degree-zero polynomial budget.

`Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run` instantiates
this profile for any minimum-degree/cycle target. Its semantic theorem is
`noProperCore`. The Erdős theorem
`properSubgraph_minDegree_le_two` specializes the conclusion to

```lean
∀ H : Graph.PackedFiniteObject.ProperSubgraph ctx.G,
  H.value.object.minDegree ≤ 2
```

`EdgeRootedNoProperCorePrefix` bundles this result with the edge-rooted CT1
and local dart-deletion CT2 prefix on `fixedContext ctx`.
`noProperCorePrefix_previous` states this provenance at the concrete Erdős
boundary.

## Nodes `[9]` and `[10]`: deletion criticality

The registered route identifier is

```text
CT1.residual.avoiding->CT2.localDeletion
```

It consumes the actual CT1 avoiding residual, transports the selected
minimality kernel through the target bridge, and performs finite local dart
discovery. The graph profile supplies dart deletion, exact edge-count
decrease, endpoint-slack baseline preservation, and cycle transport through
graph inclusion.

The concrete results are:

- `localRoute_disabled`;
- `deletionCriticality`, proving that every edge has a degree-three endpoint;
- `highDegree_independent`; and
- `VerifiedCT1CT2Prefix`, recording CT1 terminal/trace, route provenance,
  disabled discovery, return-set disjointness, and both graph consequences.

The dart schedule is derived from the declared vertex enumeration and has at
most the ordered-pair schedule size. No subgraph or ambient graph universe is
materialized.

## Nodes `[11]`–`[14]`: one boundaried-replacement CT3 stage

Chapter 1 draws four consecutive nodes, but they are one CT3 execution block:

```text
[11] boundaried atom and boundary-degree fibre
  → [12] universal outside-context response
  → [13] certified replacement compression terminal
  → [14] hereditary target-uncompressibility
```

The same CT3 semantics are invoked again by the rank-drop decisions at nodes
`[36]`–`[39]`; those later consumers are not independently implemented here.

### Reusable airtight CT3 semantics and runner

`Graph.PackedBoundariedGluing` is the sole boundaried replacement interface.
A piece is a
finite graph on `T ⊕ Internal`; an outside context is normalized to contain no
boundary--boundary edge, so those edges are owned by the piece. Every ordinary
decomposition admits this ownership convention, and replacements remain free
to change boundary--boundary edges.

The literal union gluing proves:

- the exact glued vertex count;
- disjointness of the two mapped edge sets and exact edge-count additivity;
- strict whole-graph lexicographic rank decrease from only a strict local
  piece decrease;
- exact degree formulas for replacement-internal, outside-internal, and
  boundary vertices;
- preservation of minimum degree from equal local boundary degrees and the
  replacement's internal degree bound; and
- invariance of rank, minimum degree, and the cycle-length target under the
  graph isomorphism reconstructing the selected ambient graph.

`MinimumDegreeCycleReplacement.Compression` therefore contains no asserted
whole-glue rank or baseline fact. Its mathematical fields are boundary-degree
equality, one-way obstruction inclusion, internal target-freeness, the internal
degree bound, and local lexicographic smallness. A target-complete quotient
constructs this one-way relation as a special case. `certifiedInput` derives every global obligation
before invoking the shared minimality kernel.

`CT3.CertifiedCompression` owns only the canonical typed path

```text
entry → vectorComputation → compressionSearch → compressionTerminal
```

and the reduction-kernel contradiction after the graph layer has constructed
the genuine `Core.SmallerObject`. `runCertifiedCompression_total` proves
totality and `certifiedCompressionBudget` records one degree-zero check.

The current theorem explicitly requires `Nonempty T`. This is the structural
boundary fact for a proper connected atom in a connected ambient graph. The
Lean CT3 stage does not yet derive ambient connectedness and hence does not
claim the empty-boundary whole-graph case; closed representatives belong to
the manuscript's separate closed-profile branch.

### Erdős declarations and provenance

`ConcreteCT3` is a narrow instantiation at minimum degree three and the
power-of-two-cycle target. It exports only aliases for the framework-owned
`Piece`, `Context`, `ProperAtom`, `Compression`, and `VerifiedStage` types.
Boundary-fibre separation, context universality, composition, target defects,
the compression terminal and trace, totality, work bounds, and impossibility
are consumed directly from
`Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement`; the Erdős
package does not restate those theorems under application-local names.

`verifiedBoundariedReplacementPrefix` takes the exact
`VerifiedNoProperCorePrefix` as its input. The provenance theorem
`boundariedReplacementPrefix_previous` recovers that preceding output, while
`boundariedReplacementPrefix_uncompressible` extracts the literal-gluing
node `[14]` conclusion from the composed stage. The public endpoint
`exists_verifiedBoundariedReplacementPrefix` accepts only the official
internal object, its baseline, and target avoidance.

## Nodes `[15]`–`[16]`: one induced-`P₁₃` CT1 stage

The diagram's branch test and HSS leaf are one CT1 execution block:

```text
[15] decide whether an induced P₁₃ realization exists
  ├─ avoiding → literal P₁₃-freeness
  │               → [16] HSS target cycle → contradict target avoidance
  └─ realization → proof-carrying induced P₁₃ embedding → C1 terminal
```

Node `[16]` is therefore not a separate CT. It closes the avoiding residual
of the CT1 realization decision at node `[15]`.

### Reusable induced-path profile

`StructuralExhaustion.Graph.HasInducedPath G k` is Mathlib's literal induced
containment relation

```lean
SimpleGraph.IsIndContained (SimpleGraph.pathGraph k) G.
```

Its certificate is a graph embedding `pathGraph k ↪g G`. The embedding's
injectivity supplies the distinct vertices, and adjacency reflection supplies
both the path edges and the absence of chords.

`Graph.InducedPath.Profile` generates:

- `TargetCertificateEncoding` with the embedding as its code;
- `Profile.run` and `Profile.runAvoiding`;
- positive and avoiding terminal, trace, semantic, and totality theorems;
- one-check and zero-check degree-zero polynomial budgets; and
- `VerifiedStage`, which retains an actual existential C1 execution.

`Graph.PackedMinimumDegreeCycle.inducedPathProfile` instantiates that API on
the varying-vertex packed ambient. `inducedPathInput` is definitionally the
selected minimal context's inherited branch; it does not construct a fresh
context. `EdgeRootedBoundariedInducedPathPrefix` retains the exact CT3 prefix
as `previous` and adds the induced-path stage on the same graph.
This is ordinary typed theorem composition, not a residual-to-trigger flow,
so no registered route is introduced.

### Sole external theorem

`StructuralExhaustion.Graph.External.HegdeSandeepShashank.
p13Free_hasPowerOfTwoCycle` records exactly the cited theorem: a finite
induced-`P₁₃`-free graph of minimum degree at least three contains a
power-of-two cycle.

This is the only authored axiom in the framework and external example
packages. `tools/lint_automation_first.py`, `tools/verify_lean.py`, and
`tests/test_repository.py` allow exactly this declaration at exactly its
graph-level module path. Every other axiom, admission, or unsafe declaration
is rejected.

### Erdős execution and provenance

`runP13FreeCT1` reaches

```text
entry → equivalenceCertification → realizationDecision → avoidingTerminal
```

with zero checks. `hssTarget_of_p13Free` converts its semantic residual to
the packed power-of-two-cycle target, and `p13FreeBranch_closed` contradicts
the existing `ctx.avoids`. Consequently `inducedP13_of_hss` proves the exact
realization required by `cor:p13-exists`.

For any resulting embedding, `runInducedP13CT1` reaches

```text
entry → equivalenceCertification → realizationDecision → c1Terminal
```

with one local certificate check. The application exports its semantic
theorem, totality, exact trace, and polynomial work theorem.

`verifiedInducedP13Prefix` consumes a concrete
`VerifiedBoundariedReplacementPrefix`; `inducedP13Prefix_previous` recovers
that exact input, while `inducedP13Prefix_stage` and
`inducedP13Prefix_realization` expose the new CT1 output. The endpoint
`exists_verifiedInducedP13Prefix` starts with only the official internal
object, baseline, and target avoidance.

## Node `[17]` and packing clauses of `[25]`–`[27]`: one CT12 stage

The manuscript first defines `p₁₃` as the maximum size of a vertex-disjoint
induced-`P₁₃` family, then uses maximality to make its complement
`P₁₃`-free. The implementation selects a maximum family, so both statements
come from the same object.

### Reusable core and CT12 profile

`Core.FiniteDisjointPacking.Profile` takes a finite item type, a finite vertex
schedule, one finite support per item, and a representative vertex in each
support. The framework proves:

- existence of a maximum-cardinality pairwise-disjoint family;
- maximum implies maximal saturation;
- the selected list is duplicate-free and pairwise support-disjoint;
- every other disjoint list is no longer; and
- the selected list has length at most the host vertex count, by injectivity
  of the representative map.

The maximum is selected by proof-level finite choice. No executable
definition constructs `Finset.univ` of embeddings or a powerset of packings.
`CT12.DisjointPacking.Profile.run` passes only the selected list to the
existing well-founded `CT12.ListPeeling` runner. The framework exports the
exhausted terminal, valid typed trace, totality, exactly `pₖ` iterations, at
most `n` iterations, and trace length at most `4n + 3`.

### Reusable graph layer

`Graph.InducedPathPacking` instantiates finite supports with literal Mathlib
embeddings `pathGraph k ↪g G`. It proves:

- maximum and maximal induced-path packing theorems;
- exact support size `k` for every window;
- `|W| = k pₖ`, `|R| + k pₖ = |V(G)|`, and `k pₖ ≤ |V(G)|`;
- construction of `R` as an actual `FiniteObject` induced on the vertex
  complement; and
- induced-`Pₖ`-freeness of `R` and every induced subgraph of `R`.

`Graph.FiniteObject.induceFinset` owns the reusable finite induced-subgraph
construction and canonical embedding. `Graph.FiniteObject.InternalSubgraph`
represents an arbitrary finite graph supported inside the host, and the graph
layer proves that replacing it by the induced graph on the same support cannot
lower minimum degree. The HSS module therefore proves the reusable exact
consequence that a finite `P₁₃`-free graph avoiding power-of-two cycles
contains no finite internal subgraph of minimum degree at least three.

### Erdős execution and provenance

`Erdos64EG.Internal.p13` is the selected maximum cardinality,
`p13CoveredVertices` is `W`, and `p13Remainder` is the actual induced graph
`R`. The application exports `p13_maximum`, `p13_saturated`,
`runP13PackingCT12_iterations_exact`, `p13Remainder_partition`,
`thirteen_mul_p13_le_vertexCount`,
`p13Remainder_free`, `p13Remainder_componentwise_free`, and
`p13Remainder_internalSubgraphThreeCore_free`.

`verifiedP13PackingPrefix` consumes the exact `VerifiedInducedP13Prefix`.
Its generic graph prefix derives packing nonemptiness from the induced
embedding retained by CT1, rather than accepting nonemptiness or a packing as
an input. `p13PackingPrefix_previous` recovers the exact predecessor, and
`exists_verifiedP13PackingPrefix` starts only from the official internal
graph, baseline, and target-avoidance hypotheses.

## Node `[18]`: one exhaustive attachment-label CT10 stage

The manuscript fixes an induced path `v₀…v₁₂` and assigns each outside
vertex its set of adjacent path positions. A nonempty label is legal exactly
when no two selected positions differ by `2` or `6`, since those differences
close cycles of length `4` or `8`.

### Reusable CT10 and core layer

`CT10.ExhaustiveClassification.Profile` takes an explicitly enumerated
candidate type and a decidable acceptance predicate. Its accepted subtype is
the exact class table. The profile constructs and executes the canonical CT10
capability, whose rows contain their own accepted class, and proves:

- the exhaustive terminal;
- the exact trace
  `entry → table → direct → missing → exhaustiveTerminal`;
- semantic outcome validity and typed-trace validity;
- totality with the exact terminal and trace; and
- a quadratic budget for candidate classification, direct scanning, and row
  population.

The work ledger is

```text
candidateCount + classCount + classCount².
```

`Core.Enumeration.subtype` retains the source order and constructs its
accepted enumeration directly from the already duplicate-free filtered list.
It does not perform a second quadratic deduplication pass.

### Reusable graph layer

`Graph.InducedPathAttachment` owns all path-attachment semantics independent
of the Erdős constants:

- `Label order`, `LabelCode order`, exact bit-code encode/decode equivalence,
  and the sequential `2^order` code enumeration;
- symbolic `and_shift_eq_zero_iff_no_gap`, proving for any positive gap that
  a shifted bit intersection is zero exactly when the decoded label has no
  pair at that gap, without enumerating the code universe;
- `Legal`, `Compatible`, `C`, and `omegaTwo`, with exact zero/one semantic
  theorems;
- construction of the literal path segment and the simple cycle closed by two
  attachments of one outside vertex; and
- `attachmentLabel_legal_of_avoids` and its finite-object wrapper, proving
  that target avoidance places every actual nonempty attachment in the legal
  class table.

`Graph.PackedMinimumDegreeCycle.
EdgeRootedBoundariedInducedPathPackingAttachmentPrefix` is the framework-owned
composition of the preceding CT12 packing prefix and a proved attachment
classification. It keeps the exact predecessor, stores the complete CT10
`VerifiedStage` on the inherited branch context, and exposes legality and
acceptance for every actual path attachment. This is ordinary typed theorem
composition; no residual route is involved.

### Erdős execution and provenance

`P13CodeLegal` is the constant-width bit test

```text
code ≠ 0,
code AND (code >> 2) = 0,
code AND (code >> 6) = 0.
```

`p13CodeLegal_iff_gapLegal` derives its manuscript semantics from the generic
symbolic gap theorem. `p13Legal_iff_gapLegal` separately proves equivalence to
the graph-level cycle predicate. The bounded local computations certify:

- `p13Label_candidate_count`: `8192` candidates;
- `p13LegalLabel_count`: `399` accepted labels;
- `p13LegalLabel_size_distribution`: `13,60,122,122,63,17,2` for sizes
  `1,…,7`;
- `legalP13Label_card_bounds`: every accepted label has size from `1` to `7`;
  and
- `p13Label_check_count`: exactly `167792` accounted checks.

`p13Label_checks_quadratic` states the concrete candidate-square bound used
by the generic profile.

The fixed computation is isolated behind two modules. `P13LabelKernel`
contains only the thirteen-bit definitions and CT10 profile, while
`P13LabelCertificate` contains the isolated finite-reflection reports. The
pair-gap semantic theorem is kernel-checked with `decide`; the full table
cardinality, histogram, fixed-width cardinality, legal-size report, and source
count remain behind the cached module boundary. The module imports no Erdős
proof stage after `InternalProblem`, so later edits reuse its `.olean`.
`VerifiedP13LabelAlgebraPrefix` deliberately omits the report-only table count
and histogram. Consequently the native table computation is not an axiom
dependency of the logical Erdős prefix.

`runP13LabelCT10_terminal`, `runP13LabelCT10_trace`, and
`runP13LabelCT10_total` expose the exhaustive execution, including semantic
validity and typed-trace validity. `p13C`, `p13C_eq_one_iff`, `p13OmegaTwo`,
and `p13OmegaTwo_eq_one_iff` are the exact fixed-order, power-of-two
instantiations of the manuscript relations.

`verifiedP13LabelAlgebraPrefix` consumes a concrete
`VerifiedP13PackingPrefix`. `p13LabelAlgebraPrefix_previous` recovers that
exact input, and `p13LabelAlgebraPrefix_stage` exposes the CT10 verification
package. `p13AttachmentLabel_legal` derives actual-label membership from the
existing target-avoidance proof, and `p13AttachmentLabel_accepted` transports
that result into the compact accepted-class contract. The endpoint
`exists_verifiedP13LabelAlgebraPrefix` starts only from the official internal
object, baseline, and target avoidance, and retains every earlier stage on
the same selected graph.

## Node `[72]`: CT14 hybrid-incidence refinement

`CT14.ExecutionResult.capacityResidual` extracts the actual capacity residual
from the preceding execution. The registered forced route
`CT14.residual.capacity->CT14` preserves the complete branch context and
constructs only the target CT14 capability's empty trigger. Its independent
automation-first fixture refines the generic CT14 capacity example to a
two-member Boolean ledger.

`Graph.HybridFanIncidence` owns the reusable graph semantics. For every actual
cubic-closed member it deletes the centre from that vertex's declared
neighbour list and proves that the result has length two. Its finite incidence
type is the product of the semantic closed-member subtype with `Bool`, so the
enumerator has exactly `2c` entries and at most `2|V|`. It does not construct
the rejected quadratic universe `closedMembers × V`. Each entry is proved to
be an actual assigned graph incidence. If two distinct entries reused a
non-centre endpoint, their two cubic-closed neighbours and the fan centre
would form a literal four-cycle; target avoidance therefore proves endpoint
injectivity.

The second CT14 capability labels each incidence by its computed window or
non-window kind and assigns lower mass and capacity two, measured in
quarter-units. Generic CT14 theorems now own the repeated complete-capacity
control-flow proof and binary-label multiplicity partition. The graph stage
derives

```text
I_window + I_nonwindow = 2c
totalQuarterCredit = 4c
3 ≤ 4c - (4c + k - 11)          when k ≤ 8
remainingNonWindowDemand ≤ nonWindowQuarterCredit.
```

The Erdős module supplies the literal `P₁₃` window profile, the already proved
four-cycle exclusion, and the explicit marked-fan branch input `k ≤ 8`; it
does not assert any CT outcome or count. The verified boundary is local: it
does not yet identify the local entry with the manuscript's global B1 carrier
choice or prove B2. The manuscript states the local lemma without forward
references and identifies it with B1 only after the global bridge definition.

## Nodes `[73]`–`[74]`: exact assigned-charge realization

When a fan assignment contains a decorative or packed-window shoulder outside
the counted core, the graph layer uses the exact external-shoulder identity:
assigned fan weight plus four quarter-units per external assigned shoulder is
bounded by,
and in the cubic port setting equals, the literal induced-core charge.
`Graph.WindowExternalCharge` injects every window incidence into this external
correction; it does not treat window multiplicity as free credit.

The refined reserve is canonical. A selected non-window incidence is
available only when its remote endpoint is a counted non-center vertex,
adjacent to no assigned center, with actual core quarter charge at least two.
No application-supplied `safe`, `smaller`, or reserve-correctness field is used.

For every full CT12 choice, `CT14TypeBAssignedCharge` constructs the literal
core support consumed by each candidate. It proves that this support is inside
the candidate carrier, inside the counted core, and disjoint from all assigned
centers. The framework theorem
`FiniteRefinedLedger.Choice.refinedSupport_pairwiseDisjoint` then transports
CT12 carrier disjointness to these actual charge supports. Hence the sum over
their union is exactly the sum of the local core-charge sums, with no hidden
reuse.

`Graph.AssignedSupportCharge` owns the reusable post-selection algebra. It
partitions the counted core into selected vertices, retained assigned centers,
and a literal remaining core, and proves

```text
net quarter charge
  = selected center-plus-core charge
  + retained center-core charge plus one correction per center
  + remaining-core charge.
```

The first term is nonnegative by the transferred local candidates. The second
is pointwise `4 * positiveDeficiencyAt(center)` and is nonnegative. Therefore
Lean proves the unconditional exact alternative: the Type B net charge is
nonnegative, or the literal remaining core has negative charge. The latter is
the genuine Type A continuation; it is not hidden in a certificate field or
reported as a completed Type B closure.

All new finite objects are images, filters, unions, and sums over declared
centers, ports, and selected incidences. No powerset, candidate product, graph
family, path family, or context universe is evaluated. The isolated targets
`Erdos64EG.CT14TypeBAssignedCharge`, `Erdos64EG.Tests`, and
`Erdos64EG.WebExport` build successfully.

## Node `[74]`: exact Type B-to-Type A boundary

The raw remaining term uses degree in the original Type B core, whereas
receiver discharging uses degree after the selected vertices and centers are
deleted. The boundary identity retains both coordinates and their exact
deleted-incidence difference.

`Core.FiniteReceiverDischarge` owns the reusable quarter-unit `3/7/11`
arithmetic. `Graph.LowDegreeReceiverRouting` proves from internal-three-core
freeness that every component has a degree-at-most-two receiver and builds the
proof-selected routing without evaluating a reachability table. The Erdős
application proves that the literal remaining graph is induced-`P₁₃`-free,
power-of-two-cycle-free, internal-three-core-free, and subcubic.

The application then proves the pointwise and summed boundary identities

```text
induced remaining charge
  = raw charge retained by the Type B identity
  + 4 * deleted original-core incidences.
```

Thus unsaturated receiver discharge proves nonnegativity only after adding the
explicit deleted-boundary credit. `Core.FiniteBoundaryTransfer` gives the exact
proof-level injection-or-strict-overload alternative without enumerating
transfer functions. `Graph.FiniteInducedBoundary` realizes every positive loss
as a literal cut edge and bounds the complete cut by the ambient degree sum of
the processed side.

The application proves that one local selected support has at most 24 actual
core vertices, the complete processed support has at most 25 vertices per
assigned center, and its ambient degree sum is at most 200 per center. Since
each center contributes at least one assigned-surplus unit, the boundary credit
is at most 800 quarter-units per assigned surplus. The unconditional endpoint
is therefore nonnegative net charge, an actual saturated receiver, or a strict
boundary overload with a literal landing and
`-netQuarterCharge ≤ 800 * assignedSurplus`. The manuscript B2 definition no
longer accepts boundary payment as a clause; it derives this quantitative
alternative from the finite cut.

These proofs use finset intersections, images, component reachability as a
logical proposition, and integer sums. They introduce no executable path,
subgraph, powerset, or routing-function enumeration. The targets
`StructuralExhaustion`, `Erdos64EG.CT14TypeARemainingDischarge`,
`Erdos64EG.CT14TypeBBoundaryDeficit`, `Erdos64EG.CT14TypeBPostLedger`, and
`Erdos64EG.Tests` build successfully.

## Node `[74]`: choice-free Type B deficit

`Core.FiniteReceiverDischarge` now defines the literal excess
`load - capacity` at each receiver and proves unconditionally that the
negative induced quarter-charge is at most the sum of those excesses.
`Graph.HighCenterDeletionCharge` packages the reusable graph transition:
delete every assigned high center, compare raw and induced charge across the
actual center cut, and retain the exact receiver overload of the remaining
subcubic graph. It proves

```text
-netQuarterCharge ≤ 21 * assignedSurplus + receiverOverload.
```

The constant is derived as `4` units for the assigned center surplus, `1`
unit for the number of centers, and at most `16` units for the quarter-scaled
center cut. No local candidate or B2 disjointness is used.

`CT14TypeBUnconditionalDeficit` instantiates this theorem on every literal
`TypeBSupportScope`. The counted core is a subset of the verified packed-path
remainder; after all actual degree-at-least-four centers are deleted, every
retained vertex has ambient degree three. The remaining graph is proved
`P₁₃`-free and dyadic-cycle-free, so the sole external HSS theorem supplies
internal-three-core-freeness. The resulting Type B bound applies before the
unresolved/full-resolution split and therefore also on every minimal-overlap
branch. The overload term is the exact Type A continuation, not an assumed
contract field.

## Node `[126]`: CT12 sparse upper envelope

`Graph.DegeneracyPeeling` owns the reusable bounded elimination certificate,
its existence proof from `InternalMinDegreeFree (bound+1)`, the exact CT12
runner, exhausted terminal, expected trace, semantic validity, totality, and
linear work certificate. Its sharp two-degenerate theorem counts at most two
edges per deletion until two vertices remain and then uses the universal
one-edge bound.

`CT12SparseEnvelope` selects an actual cubic vertex from deletion criticality,
forms the literal induced complement, and obtains its core freeness from the
already verified packed no-proper-core theorem. The exact CT12 execution has
one iteration per remaining vertex. Restoring the selected vertex through the
generic induced-edge recurrence proves `m≤2n-2`.

`Graph.SurplusPortActivity.degreeExcess_sum_int_eq` proves the reusable
handshake bridge from an ordered degree-excess ledger to `2m-3n`. Thus the
existing CT6 ledger is exactly the manuscript surplus, and Lean verifies both
node `[126]` identities `σ=n-6-2λ` and `2m=3n+σ` over the integers. The public
endpoint accepts only the official finite graph, its baseline, and target
avoidance, and retains `VerifiedTypeBPostLedgerPrefix` as its `previous` field.

## Node `[129]`: CT15 baseline spine demand

`CT15.BaselineDemand.Profile` is the reusable author interface for a finite
independently target-testable coordinate family, its exact baseline budget,
and its deficit. The framework supplies unit charges, the target-relative
rank pass, the first-drop scan, the exact ledger and total, the deterministic
full-rank terminal and trace, soundness, totality, and a linear polynomial
work budget.

`CT15BaselineSpineDemand` computes

```text
N = choose(n, 2)
m₀ = ceil(3n/2)
S₀ = choose(N, m₀)
b₀ = Nat.log2 S₀.
```

It instantiates the profile with the canonical empty coordinate family. This
family is independently target-testable vacuously, has cardinality zero, and
has exact deficit `b₀`, so `0 ≥ b₀-b₀`. CT15 scans this complete declared
universe and returns the full-rank-ledger terminal. The public endpoint takes
only `object`, `baseline`, and `avoids`, and retains the complete sparse-
envelope prefix as its `previous` field.

The manuscript definition does not construct a nonempty family or prove an
`O(n)` deficit. The Chapter 1 diagram and ledger now state this accurately:
the linear deficit is a separate downstream estimate required by the entropy
sandwich, and is not imported into this verified endpoint.

## Independent transfer

`MantelExample.K34OpenPortSuppression` independently instantiates the exact
`Graph.OpenPortSuppression.Setup` contract on the textbook complete bipartite
graph `K₃,₄`.  It supplies the four named local vertices, verifies the
cubic endpoint neighbourhood and open shoulder pair, and then obtains both
minimum-degree preservation and strict packed-rank decrease from the shared
graph theorems.  The example performs no path, subgraph, context, or graph
enumeration.

The independent transfer is
`EvenCycleExample.CT14HighCenterDeletionCharge`. It instantiates the same
`Graph.HighCenterDeletionCharge.Profile` on the textbook complete bipartite
graph `K₃,₄`: the three degree-four vertices are the complete high-center
set, the four degree-three vertices form the retained edgeless graph, and
internal-three-core-freeness is proved directly without the external HSS
theorem. The theorem
`ConcreteK34.highCenterDeletion_deficit_bound` is the exact generic
`21 * assignedSurplus + receiverOverload` conclusion.

`GreedyColoringExample.DegeneracyTriangle` independently instantiates the
same `Graph.DegeneracyPeeling.Profile` on the textbook triangle `K₃`. It runs
the exact public CT12 machine, proves the exhausted terminal and expected
trace, typed trace validity, totality, exactly three iterations, the linear
polynomial budget, and the sharp edge bound. Its core-freeness proof uses only
the generic finite simple-graph vertex-count theorem and no external axiom.

`StructuralExhaustion.Examples.CT15AutomationFirst.threeSwitchDemand`
independently instantiates the same baseline-demand profile on the textbook
three-coordinate Boolean switch family. Its baseline is five units, its
deficit is two, and its three unit-charge coordinates exactly meet the lower
bound. The public profile returns the full-rank-ledger terminal, exact
six-node trace, ledger total three, and linear work certificate.

`examples/even_cycle/EvenCycleExample/CT2Audit.lean` instantiates the exact
`Graph.PackedMinimumDegreeCycle` and `CT2.CertifiedReductionInput` APIs with
the textbook even-cycle target. It exports:

- `exists_noProperCorePrefix`;
- `properCoreCT2Run_terminal`;
- `properCoreCT2Run_trace`;
- `properCoreCT2Run_checks`; and
- `properSubgraph_minDegree_le_two`.

The same package also instantiates the fixed-vertex local-deletion route and
its degree-three endpoint theorem. Reusable rank, subgraph, cycle transport,
runner, totality, and work-bound proofs live in the framework.

`examples/even_cycle/EvenCycleExample/Concrete.lean` independently
instantiates `Graph.SurplusPortActivity` for the even-cycle `K₄` fixture.
It verifies the same CT6 active-ledger terminal and the zero-surplus total
without using the Erdős power-of-two length predicate.

The same file also instantiates `Graph.HybridFanIncidence` for an arbitrary
minimum-degree cycle target. It separately verifies endpoint injectivity,
the three-quarter-unit slack theorem, and the routed CT14 capacity terminal,
without importing any Erdős declaration.

`EvenCycleExample.CT3SeriesReduction` supplies the independent textbook
Duffin parity-series coordinate model and additionally constructs
`exists_duffinConcreteBoundariedReplacementStage` at boundary `Fin 2`, using
the same literal packed-graph stage. This is the non-Erdős transfer
fixture for the local-to-global gluing theorem.

`examples/even_cycle/EvenCycleExample/CT1InducedEdge.lean` independently
instantiates the exact `Graph.InducedPath.Profile`. It proves the textbook
fact that every selected graph edge is an induced `P₂`, executes the same
certificate-driven runner, and exports its C1 terminal, exact trace, semantic
theorem, totality, one-check polynomial bound, and a concrete `K₄` execution.

`examples/even_cycle/EvenCycleExample/CT12MaximalMatching.lean`
independently instantiates the new `Graph.InducedPathPacking` profile at
`k = 2`. Its selected windows are a maximum matching, its CT12 run reaches
the exhausted terminal in exactly the matching-number many iterations with
the same vertex-linear bounds, the exact
partition is `|R| + 2p₂ = |V|`, and maximal saturation proves that the
unmatched remainder is edgeless.

`examples/mantel/MantelExample/CT10EdgeAttachment.lean` independently
instantiates the exact compact-label and CT10 profile for the textbook local
step in Mantel's theorem. An induced edge has four possible attachment labels
and exactly two legal nonempty labels, both singletons. The package proves
candidate count `4`, class count `2`, check count `10`, the exhaustive
terminal and exact typed trace, and singleton cardinality. Mathlib's
`is3Clique_iff_exists_cycle_length_three` converts `CliqueFree 3` into the
cycle-avoidance premise of the shared graph theorem, so every actual nonempty
attachment to the edge is accepted by the same classification contract.

## Current dependency-ready endpoint

### Part I nodes [22]--[24]: audited repair boundary

Node [21] now supplies the exact 91-row multi-scale curvature computation,
including the safe/flat products and the strict integer rate floor. It does
not supply a Boolean product realization.

The reusable repair support is compiled and imported:

- Core.LocalBooleanRealization exhaustively returns either a complete local
  Boolean realization or the first omitted assignment.
- Graph.LocalBooleanWindowLedger partitions an explicit finite window family
  into those two outcomes.
- P13ActualAttachmentResponse constructs the graph-owned 13-coordinate
  attachment system of one selected window. It deliberately does not identify
  those coordinates with the 91 curvature barriers.
- Graph.InducedPathColdLedger proves the graph-owned node-[151] surplus
  filter and node-[152] identities: an ambient-cubic selected P₁₃ has
  exactly 15 external stubs and 13 stubs after the two transit ends.
- Core.FiniteFirstFailure, Core.FiniteBoundedOverlap, and
  P13ColdGermLedger provide the finite first-failure, disjoint extraction,
  and G1/G2/G3 classifier layers.
- Core.FiniteSequentialFiltration computes either the first exact
  ratio-failing conditional fibre or a complete telescoping product ledger.
  P13SequentialEntropyFiltration instantiates its weights with node [21] and
  proves the exact 118-bit state loss when the complete terminal fibre is
  nonempty; it does not assume that nonemptiness or a graph state universe.
- Routes.SequentialRatioFailureHandoff retains a computed P13 failure's exact
  barrier, index, conditional fibres, strict arithmetic inequality, and
  branch/profile provenance. P13SequentialRatioFailureAudit records the
  current 13-coordinate graph interface versus the 91-row node-[21] table.
  No CT6/CT7/CT10 label is attached without a graph reflection theorem.
- P13MultiScaleConnectorState constructs the first actual 91-barrier state
  layer without caller state data. It scans `91 * n^15` literal bounded
  connector sequences per selected window, verifies outside/simple/adjacent
  path clauses and the exact safe relations, and returns all connectors
  present or the first missing barrier. Its flat response is the literal
  `C_(a+b)` test. Coordinatewise connector choices are explicitly not a
  global graph completion or commuting product.
- Graph.InducedPathColdCorridor and P13ColdCorridorProducer construct a
  canonical deleted-edge return from an actual cold cubic stub. Their quiet
  result is an honest structural germ bounded by the ambient vertex count,
  with an explicit short/long scale split; it is not promoted to a
  constant-size target-relative germ.
- Routes.LongFiniteSupportHandoff and P13ColdScaleHandoff retain the exact
  long-corridor length, scale inequality, selected stub/germ, branch context,
  and canonical finite position enumeration. They are deliberately pre-CT17:
  no target/offset/value/compatibility semantics or finite scale limit is
  inferred from length alone.
- P13ColdGermTerminalRoutes executes a supplied G1 witness through CT1,
  converts G2 to the literal target-defect residual, and executes G3 through
  the graph-owned CT3 compression.
- Routes.TargetDefectHandoff and P13ColdTargetDefectHandoff retain the two
  pieces and exact distinguishing context. This is a verified residual, not
  an exit-(4) or contradiction claim.

Nodes [22]--[24] remain non-green. The first missing producer is the
finite dyadic-scale completion-state system for an actual selected window.
It must construct a response evaluator and a nonvacuous graph-owned
multi-scale state family. Cross-window multiplication additionally requires a
commuting gluing theorem or a different proved global account. The cold side
still requires a constant target-relative response code or a terminating
long-scale route, the overlap constant, promotion to a real hit/defect/
compression payload, and an admitted target-defect consumer.
Consequently no P13CoverageResidual with the manuscript's numerical ceiling
is currently constructed, and node [25] is not invoked from node [24].

### Node-local coverage audit

The compiled Chapter 1 descriptor has no partially formalized nodes.

- Node `[3]` is unconditionally verified by
  `Erdos64EG.Internal.officialConclusion_of_notCounterexample`.  Its inputs
  are the exact negative result of the node-`[2]` predicate on the same graph
  and the official minimum-degree baseline; its conclusion is the official
  power-of-two-cycle statement for that graph.  The generic logical step is
  owned by `Core.target_of_not_isCounterexample`.
- Nodes `[64]`, `[65]`, and `[66]` are paper-only.  They denote respectively
  the negative-net-charge Type B continuation, the assigned Type B support
  join, and the Type A exit-`(7)` handoff.  Their incoming residuals from
  nodes `[57]`--`[63]` and `[108]` are not outputs of the verified prefix, so
  no implemented local-port stage claims those nodes.
- High-centre neighbourhood, port-classification, open-pair, response, and
  shoulder-ledger declarations are indexed only to the local nodes they
  prove: `[67]`--`[69]`, `[78]`--`[79]`, and `[130]`.

`exists_verifiedHomogeneousPatternPrefix` is the unconditional endpoint of
the Part X branch. It chains only green predecessor outputs on the identical
selected graph:

- `VerifiedAllPairTokenRoutingPrefix` supplies the exact complete pair list,
  the blocker decision, every canonical first hit, and each free-anchor token;
- `Graph.SurplusCapacityTokenRouting` refines that same list to the disjoint
  window/remainder/primitive token sum. The admitted candidate type proves
  node `[133]`'s raw audit kinds impossible, the priority map is total on every
  blocked pair, and the 25-role labels partition every pair exactly once;
- `Graph.InducedPathWindowLedger` uses only the selected maximum `P₁₃`
  packing and proves the exact node-`[135]` supply `15p₁₃+σ_W`;
- generic `CT9.ClasswiseTokenLedger` executes the node-`[137]` comparison on
  the literal complete pair count. Its positive result contains the actual
  first overloaded label, while its other result contains only the proved
  aggregate capacity inequality;
- `Graph.SurplusClasswiseOverload.routeClass` inspects the overloaded token's
  sum constructor and proves the exhaustive node-`[139]`/`[141]` route; and
- `noCoupledOverload_quadraticSpine` combines the exact unordered-pair count,
  25 roles, `|T_cap|≤9n`, and `σ≤n` to prove
  `σ²≤(450bmax+1)n` at node `[138]`; and
- `Graph.SurplusHomogeneousPattern.audit` consumes the literal overloaded
  fibre and its window/remainder/primitive route. Its generic greedy maximal
  matching covers every supplied pair; the sharp endpoint-incidence cap
  returns a matching or star of the selected class threshold at nodes
  `[140]`, `[142]`, and `[143]`.

Six unconditional endpoints cover the green side boundaries without
changing their residual inputs:

- `exists_verifiedSurplusScaleSplitPrefix` consumes node `[18]` and makes
  the exact node-`[19]` squared-scale decision;
- `exists_verifiedP13PositiveDeficiencyPrefix` consumes the node-`[27]`
  remainder and computes the exact node-`[28]` positive deficiency; and
- `exists_verifiedP13CurvaturePrefix` consumes that exact remainder and
  completes nodes `[29]`--`[35]`, including both surplus-aware stub
  inequalities, the exact wedge family, and its CT15 execution;
- `exists_verifiedP13ProperDelocalizationPrefix` retains the verified generic
  rank-drop route at nodes `[36]`--`[39]` and completes the boundary-fixing
  proper/whole support split at nodes `[40]`--`[42]`; and
- `exists_verifiedP13GlobalRankClosurePrefix` consumes the exact whole payload
  at nodes `[43]`--`[47]`, derives injectivity from the already-admitted
  quotient's certified-reduction field, closes the literal node-`[46]`
  rank-drop identification, and reaches the unconditional full-rank join; and
- `exists_verifiedTypeBResidualCenterLedgerPrefix` retains the exact
  node-`[80]` certificate marking, exhausts nodes `[81]`--`[83]` through
  unresolved/full-choice/minimal-overlap outcomes, and proves node `[75]`'s
  ordinary assigned-surplus payment.

No Boolean-product realization, baseline-deficit estimate, global graph
count, matching enumeration, graph universe, context universe, path family,
or recursive search tree is an input to these stages. Both complete CT9
product scans have the explicit bound `225n³`.

`MantelExample.CT15EdgeResponses` independently instantiates the exact
finite-support response and admissible-quotient CT15 contracts on the textbook
edge `K₂`, and also instantiates the graph-generic positive-deficiency/wedge
kernel on its complete two-vertex support.  Its `K4Repair` namespace applies
the literal graph-level one--three repair theorem to `K₄`, computing four
internal cubic vertices, no boundary leaves, cycle rank three, and zero
surplus.
`MantelExample.CT9EndpointRoleLedger` independently executes the same exact
token--role CT9 profile on the two labelled endpoints of `K₂`, including
partition, the exact overloaded terminal and four-node trace, validity,
totality, and the concrete eight-check budget. The reusable CT9 layer derives
that terminal and trace for every nonempty zero-capacity product ledger; the
transfer proof uses only standard Lean axioms.
`StructuralExhaustion.Examples.CT9ClasswiseTokenLedger` independently
instantiates the new generic classwise profile on five textbook records, two
tokens, two roles, and two token classes. It proves exact partition, total
capacity four, the executable overload/within-capacity decision, and the
twenty-comparison work count without importing any Erdős declaration.
`MantelExample.GreedyMatchingStar` independently executes the same public
`Core.GreedyMatchingStar.verifiedStage` method on the six edges of the
textbook graph `K₄`, returns a literal size-two matching or star, and proves
the exact 108-check count and the shared quadratic work certificate.  The
framework-local `StructuralExhaustion.Examples.GreedyMatchingStar` fixture
also pins the underlying extractor without serving as the external transfer.
`StructuralExhaustion.Examples.QuadraticScaleSplit` independently verifies
both sides of the same squared-scale decision on the concrete comparisons
`7²>3·16` and `6²≤3·16`.

Exactly 84 Chapter 1 nodes are green. Nodes `[20]` and `[125]` retain the
strict node-`[19]` scale branch through the typed Part X route. Node `[46]`
closes the whole-support
rank-drop payload because its quotient is already admitted and therefore
injective by certified reduction and minimality. The open Part X frontier is node
`[144]`, which may consume only the verified matching--star pattern from
node `[140]`, `[142]`, or `[143]`. The open degree-four Type B frontier is
node `[84]`, which receives the explicit certificate-failure, unresolved
local-entry, and minimal-overlap residuals. A linear baseline-deficit estimate
and the grouped-envelope fan-mass coefficient are not assumed by any green
endpoint.

The following checks were run on 2026-07-15 for the 78-node boundary:

```text
lake build StructuralExhaustion
lake build StructuralExhaustion.Examples.GreedyMatchingStar +  StructuralExhaustion.Examples.QuadraticScaleSplit
lake build MantelExample.GreedyMatchingStar MantelExample
lake build Erdos64EG Erdos64EG.Tests Erdos64EG.WebExport
  passed

make example-export
  Framework and all four external example packages passed
  Erdős raw-export validation passed

python3 tools/render_example_catalog.py \
  --raw-root build/example-exports --root . --source-root . \
  --catalog generated/lean-machines.json
  Rendered 4 compiled Lean examples
  Erdős descriptor contains exactly 78 formalized node IDs
  The five newly implemented nodes belong to one exact composite audit;
  no green diagram node is partial
  Nodes 22, 84, and 144 are the mathematical frontier; only 84 and 144 have
  non-implemented web steps, while 22 is correctly white rather than yellow

npm run test -- --run src/erdos-proof-flow.test.ts \
  src/components/GraphCanvas.test.ts \
  src/components/ManuscriptFragmentViewer.test.tsx
  3 test files and 8 tests passed

UV_CACHE_DIR=/tmp/uv-cache uv run --offline \
  --with-requirements requirements.txt python -m pytest -q \
  tests/test_example_catalog.py tests/test_web_api.py tests/test_skills.py
  28 tests passed; 1 repository-state test failed because the pre-existing
  modified framework/branch_closure_methodology_extended.tex and generated
  PDF trigger the retired-architecture vocabulary check

lake env lean Erdos64EG/AxiomAuditTemp.lean
  ClosedRankDrop.rankDrop_impossible, OneThreeRepair.Component.identity, and
  routeRankDropThroughGlobalClosure use only Lean's standard logical axioms
  exists_verifiedP13GlobalRankClosurePrefix additionally uses only the
  permitted HSS theorem

latexmk -pdf -silent -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/erdos64-proof-build erdos_64_proof.tex
  Manuscript passed after three reference-stabilizing runs

git diff --check
  passed

make lint
make validate
UV_CACHE_DIR=/tmp/uv-cache uv run --offline \
  --with-requirements requirements.txt python -m pytest -q
  Repository-wide validation remains blocked by the checked-in
  framework/branch_closure_methodology_extended.tex terminology and the
  generated PDF that the automation-first linter classifies as a retired
  surface. generated/kernel-verification.json consequently remains failed.
  The focused Erdős catalog, Lean, web, skill, and manuscript checks above pass.
```

### 2026-07-16 node-[22] review gate

The review pass removed node `[22]` from the implemented node-`[21]`
cross-reference. The compiled descriptor therefore has exactly 78 green
nodes, no partially formalized (yellow) nodes, and leaves `[22]` white.
`P13PartIVFiniteRouting` is compiled downstream infrastructure only: it
requires the node-`[24]` coverage residual and cannot produce or bypass
node `[22]`.

Node `[22]` cannot be promoted honestly from the current contracts. The first
missing producer must construct a graph-owned finite completion-state family
for every selected window, all 91 response predicates with reflection to the
node-`[21]` relations, a nonempty terminal fibre or typed consumers for every
failure, and a commuting cross-window gluing/global injection. No existing
CT or route supplies those facts from node `[21]`'s finite arithmetic table.

The following gates passed after the cross-reference correction:

```text
lake build Erdos64EG.WebExport
  3405 jobs passed

make export
  framework and all four examples built; 4 descriptors rendered

generated/examples/erdos-64.json
  78 formalized node IDs; implemented-step references outside that set: none

git diff --check
  passed
```

### 2026-07-16 non-enumerative Part-IV correction

The fixed node-`[21]` curvature computation is now green: it checks only the
paper's constant local universes (399 legal labels and 91 barriers). It does
not enumerate graphs or assert a Boolean-product realization. The compiled
web descriptor contains 78 green nodes, with `[22]`--`[24]` and
`[48]`--`[56]` still non-green.

Ambient-size connector, short-path, attachment, and Boolean-state prototypes
remain available as standalone audit modules, but are absent from the Erdős
production import graph. The default graph umbrella also no longer re-exports
the experimental cold-search modules. No valid theorem was deleted.

The replacement cold prerequisite is split into verified structural layers:

- `Core.FixedTwoBoundaryCutState` stores only capped boundary roles, two fixed
  window offsets, thirteen dyadic response bits, and a fixed D4--D7 alphabet;
- `Graph.InducedPathColdSkeleton` records the same-component cyclic successor
  and canonical component path as proof-carrying structural data, rather than
  scanning all stubs or paths; and
- `P13FixedColdCutState` specializes the target bits to `PowerOfTwoLength` and
  requires an explicit pair-specific context comparison. Equal coarse codes
  alone never imply CT3 completeness.

The closure-robust repair has a verified same-context node-`[47]` to
node-`[55]`/`[56]` arithmetic composition, but its red-team verdict remains
FAIL because no production theorem yet inhabits
`P13WindowDensityStructuralTheorem`. The exact missing graph theorem must
derive the node-`[24]` packing ceiling and strict finite quarter budget from
the fixed cold-skeleton F2--F5 route. Nodes `[48]`--`[54]` are not used as a
rank-to-Boolean shortcut.

Current verification:

```text
lake build StructuralExhaustion
  3380 jobs passed

lake build StructuralExhaustion.Graph.InducedPathColdSkeleton \
  StructuralExhaustion.Core.FixedTwoBoundaryCutState \
  StructuralExhaustion.Examples.FixedTwoBoundaryCutState
  3126 jobs passed

lake build Erdos64EG.P13FixedColdCutState Erdos64EG Erdos64EG.Tests \
  Erdos64EG.WebExport
  3378 jobs passed
```

### 2026-07-16 node-[158] pointwise actual-attachment fork

Node `[158]` is green.  With the subsequently reviewed nodes `[159]` and
`[155]`, the Chapter 1 total is exactly 81 green nodes.
For one supplied selected induced-`P13` window, the production theorem executes
the literal actual outside-vertex-by-thirteen adjacency classifier. Its hot
constructor is impossible because the all-true assignment at positions 0 and
2 produces a four-cycle. The retained cold constructor contains the canonical
missing assignment, the exact node-`[21]` predecessor, and the same selected
window.

This is a parallel pointwise branch. It neither proves nor refutes the white
91-coordinate realization edge `[21]`→`[22]` (now displayed as node `[160]`)
and supplies no density estimate. The worst-case reference budget for one supplied
window is at most `8192*n` assignment/state vector comparisons, each comparing
thirteen adjacency bits, equivalently at most `106496*n` bit comparisons. The
subsequent corridor/path work is excluded from node `[158]`.

The TeX dependency diagram, detailed and correspondence tables, WebExport
stage and exact proof step, frontend proof-flow edge, README, and focused count
test are synchronized to this boundary.

### 2026-07-16 nodes `[159]` and `[155]`: same-window frontier and dyadic closure

Node `[159]` now consumes the exact node-`[158]` cold-fork value and executes
only the existing graph-owned selected-window route.  Its exhaustive result
has four constructors: a high-degree position in the selected window, a
dyadic target hit on the canonical restored root cycle, a first high-degree
corridor event with its clean prefix, or a quiet `ColdStructuralGerm`.  The
result retains the identical selected window and canonical external stub.
The quiet constructor has only the ambient bound `support.length ≤ n`; it is
not promoted to `ColdBoundedGerm`.

The visible certificate-verification ledger for one supplied window is
`26 + (15*p13 + windowSurplus) + n`: two possible scans of the thirteen path
positions, one scan of the existing external-incidence token schedule, and at
most `n` event checks on the proof-carrying simple return.  This is not a
constructive runtime claim for the classical return-path certificate.

Node `[155]` is green only for node `[159]`'s computed dyadic constructor.
`P13ComputedDyadicBranch` records equality with that constructor, and the thin
adapter reconstructs `ColdDyadicHit` from its exact stub position and restored
root cycle.  The existing CT1 G1 runner reaches `.c1` with its exact four-node
trace in one supplied-certificate check, and `ctx.avoids` closes the branch.
No independent target witness is accepted.

The surplus, corridor-high, and quiet constructors remain typed open
residuals.  Nodes `[153]`--`[154]`, `[156]`--`[157]`, all aggregate cold-mass
claims, and node `[160]`'s 91-coordinate completion/commuting-realization
obligation remain white.  The compiled descriptor has exactly 81 green nodes,
zero yellow nodes, and no implemented-step reference outside the formalized
set.

### 2026-07-16 node `[161]`: quiet-germ D1--D3 base-scale split

Node `[161]` consumes only a proof-carrying equality with node `[159]`'s
computed quiet constructor.  Its input retains the exact node-`[158]` fork,
selected window, canonical stub, same-window equality, no-event proof, and
`ColdStructuralGerm`; an arbitrary caller-supplied germ cannot enter this
route.

The fixed threshold is
`Qbase = 4^2 * 13^2 * 2^13`.  The theorem
`p13ColdD1D3BaseThreshold_eq_stateCard` proves that this is exactly the
`FixedTwoBoundaryCutState.State (Fin 0)` cardinal: two capped boundary-degree
roles, two window offsets, and thirteen target-response bits.  The empty
additional coordinate type is not claimed to encode D4--D7.

`runP13SameWindowBaseScaleSplit` executes the existing graph-owned
`InducedPathColdGermScale.route` once.  Its exhaustive theorem has exactly the
literal `support.length ≤ Qbase` short residual and the strict
`Qbase < support.length` long residual.  The visible work ledger is one
natural-number comparison; node `[159]` already accounts for corridor
construction and scanning.

The compiled boundary now has exactly 82 green nodes and zero yellow nodes.
Nodes `[160]`, `[162]`, and `[163]` remain white.  Node `[161]` proves no
repetition, D4--D7 semantic completeness, bounded-germ promotion, CT3
compression, or density estimate.

### 2026-07-16 nodes `[162]` and `[163]`: exact short-root and long-prefix consumers

Node `[162]` consumes equality with node `[161]`'s computed short constructor,
not an arbitrary bounded return.  The retained quiet germ and minimum-degree
context prove that the exact deleted-return root is cubic.  The graph-owned
`DeletedEdgeReturnThirdIncidence` runner uses the first return step and restored
dart as two distinct incidences, selects the declared-order third incidence,
and returns exactly on-support membership or outside-boundary nonmembership.
Its conservative visible ledger is at most `2*n + 3 + Qbase` checks on this one
root and supplied support.

Node `[163]` consumes equality with node `[161]`'s computed strict-long
constructor on the identical branch context.  The reusable
`LongFiniteSupportHandoff.route` preserves the literal support length and
`Qbase` scale, embeds the first `Qbase+1` positions, identifies the unique
overflow image at `Qbase`, and exposes exhaustive base/overflow and
prefix/after-prefix classifiers.  Constructing the handoff scans nothing;
classifying one supplied position uses one natural-number comparison.

The Chapter 1 boundary is exactly 84 green nodes.  Node `[160]` remains the
white 91-bit realization obligation.  Nodes `[164]`, `[165]`, and `[166]`
remain white: they must respectively supply long-prefix state-label/repetition
semantics, a sound non-root-chord consumer, and a sound outside-boundary
consumer.  Nodes `[162]` and `[163]` do not claim any of those conclusions,
nor D4--D7 completeness, CT3/CT17 execution, or density.

### 2026-07-16 nodes `[165]` and `[166]`: exact short-return branch consumers

Node `[165]` consumes equality with node `[162]`'s computed on-support
constructor.  The graph-owned resolver scans only the supplied
`Qbase`-bounded support, constructs the literal chord at its canonical index,
and decides that one length.  An accepted power-of-two chord closes through
the existing certificate-driven CT1 runner.  The surviving constructor retains
the exact graph-owned deleted-edge return and proves its length is strictly
smaller.  Its visible work is at most `Qbase + 1`.

Node `[166]` consumes equality with node `[162]`'s computed outside
constructor.  It retains the same oriented incidence from the literal return
support to the selected outside endpoint, packages the already certified cubic
root as a three-leaf star, and proves those leaves own every ambient incidence
at that root.  This projection performs zero additional primitive checks.

The Chapter 1 boundary is exactly 86 green nodes and has zero yellow nodes.
Nodes `[160]` and `[164]` remain white.  Node `[167]` is the white proof-level
normalized one-return rejoin: it must combine the node-`[165]` shorter return
and node-`[166]` original outside return while retaining the inherited bound,
strict decrease on the chord branch, the outside incidence, and cubic
ownership.  Node `[168]` is the separate white packed-support transition from
that normalized return; no cold-subfamily aggregate or successor/path semantics
is assigned to it.  Neither green node claims normalization, return iteration
or termination, D4--D7 completeness, CT3 execution, or density.

### 2026-07-16 node `[167]`: normalized one-return boundary rejoin

Node `[167]` accepts exactly two branch-indexed inputs over the same computed
node-`[162]` short residual: node `[165]`'s exact rejected-chord computation or
node `[166]`'s exact outside-boundary computation. On the chord branch it
selects the exact shorter return and the old first step as the outside
incidence; on the outside branch it retains the original return and selected
third endpoint. Both branches retain cubic ownership of every root incidence,
support at most `Qbase`, and selected length at most the original. The chord
branch remains strict and the outside branch remains equal. The proof-only
normalization performs zero additional primitive checks.

The Chapter 1 boundary is exactly 87 green nodes and has zero yellow nodes.
Nodes `[160]` and `[164]` remain white. Node `[168]` remains the white
packed-support transition from node `[167]`; it is not a cold-subfamily
aggregate or successor/path theorem. Node `[167]` constructs no return
iteration or termination, D4--D7 coordinate, CT3 input, or density estimate.

### 2026-07-16 node `[168]`: normalized-return packed-support transition

Node `[168]` consumes equality with one exact computed node-`[167]` normalized
return. It views that return in the ambient graph and scans its edge indices
against the union of all ambient-cubic selected-window supports. The exhaustive
result is either full containment of the return support in that union or the
first oriented membership transition, retaining its exact `BoundaryStub`,
outside endpoint, and induced-remainder component.

If `p` is the selected-window packing number, `n` the ambient order, and `L`
the one return length, the visible ledger is exactly
`13*p*n + 13*p + 26*p*L`. The disjoint packing bound `13*p ≤ n` and inherited
`L ≤ Qbase` give `n^2 + (2*Qbase + 1)*n`.

The Chapter 1 boundary is exactly 88 green nodes and has zero yellow nodes.
Nodes `[160]` and `[164]` remain white. Node `[169]` is the white all-inside
packed-return consumer; node `[170]` is the white successor/second-stub and
component-path producer. The ambient-cubic support union is not the
manuscript's selected cold subfamily, so node `[168]` proves no cold aggregate,
successor, second stub, component path, iteration, D4--D7 statement, CT3
execution, or density estimate.

### 2026-07-16 node `[169]`: ambient-cubic owner sequence and first cross-window edge

Node `[169]` consumes equality with node `[168]`'s exact computed `allInside`
constructor on the same normalized return. It prepares the ambient-cubic slot
inventory once, performs exactly one owned-slot lookup per path vertex, stores
the owner window and position in an aligned table, and compares consecutive
stored owners. The no-change constructor is impossible: the final endpoint
fixes the original selected stub window as owner, while the initial stub
neighbour lies outside that window's support. The surviving constructor is
therefore the exact first edge with distinct owners. It retains both endpoint
windows and positions, the literal adjacent path vertices, and two oppositely
oriented tokens whose subtypes are exactly `crossWindow`.

For packing number `p`, ambient order `n`, and return length `L`, the exact
local ledger is `13*p*n + |supp Γ'|*13*p + L`: the prepared cubic inventory,
one finite owner lookup per support vertex, and one comparison of stored
owners per edge. The packing bound and inherited `Qbase` support and length
bounds give `n^2 + Qbase*(n+1)`.

The Chapter 1 boundary is exactly 89 green nodes among 171 total and has zero
yellow nodes. Nodes `[160]`, `[164]`, `[170]`, and `[171]` remain white. The
owner table ranges over all ambient-cubic selected windows, not the manuscript
cold subfamily. Node `[169]` proves no successor, target-cycle closure, cold
aggregate, D4--D7 coordinate, CT3 input, or density estimate; node `[171]` is
the exact white cross-window-edge consumer.

### 2026-07-16 node `[171]`: cross-window token-pair residual

Node `[171]` consumes the complete computed node-`[169]` first-cross-window
package and invokes the reusable `InducedPathCrossWindowTokenPair` route. The
output retains exactly the two source tokens, their endpoint windows and
positions, and their literal adjacent vertices. It proves the tokens distinct,
keeps both exact `crossWindow` subtypes, records the two opposite oriented
contributions, and identifies their common undirected edge. Equality of the
tokens would identify their owner windows and contradict node `[169]`'s exact
owner change.

The route is a proof-carrying projection and performs exactly zero additional
primitive checks. The non-Erdős one-edge owner-change fixture independently
executes the same route and pins both token endpoints.

The Chapter 1 boundary is exactly 90 green nodes among 171 active nodes and has
zero yellow nodes. Nodes `[160]`, `[164]`, and `[170]` remain white. Node
`[171]` is the exact terminal residual of the all-inside branch and constructs
no repeated owner, second connector, cycle, cold-family
membership, demand or capacity bound, successor, target closure, CT execution,
or density estimate.

### 2026-07-16 node `[170]`: component boundary schedule and BFS path

Node `[170]` consumes equality with node `[168]`'s actual computed
first-transition result, retaining its exact boundary stub, outside endpoint,
and returned induced-remainder component. The reusable graph package computes
one outside BFS finset and uses it literally for the proof-carrying return-exit
scan, component predicate, explicit `WindowIndex × Fin 13` first-hit search,
complete incident-stub filter, and component object. The selected second stub
is distinct from the anchor. The actual incident schedule is complete,
duplicate-free, and has length at least two, so genuine cyclic `List.next`
provides a fixed-point-free successor in the same component. Declared-order BFS
then supplies a shortest path between the two outside endpoints.

The full ledger contains the window ledger, `13*p` slot scan, the return-length
times outside-cardinality component lookups, the outside BFS budget, the
quadratic component restriction, the actual token-filter cost, and the final
component BFS budget. Both BFS budgets have separate polynomial bounds, and
the complete total is at most `50 * localScale^3`. A non-Erdős fixture executes
the same graph package and checks the computed exit, first-slot provenance,
cyclic successor, shortest path, and work bound.

The Chapter 1 boundary is exactly 91 green nodes among 172 active nodes and has
zero yellow nodes. Nodes `[160]`, `[164]`, and `[173]` remain white. Node
`[173]` is only the component two-boundary observation consumer downstream of
`[170]`. This short first-transition branch is incompatible with the long
node-`[163]` prefix branch and its node-`[164]` state-label/repetition consumer;
there is no edge `[173]`→`[164]`. Node `[170]` proves no D4–D7 label,
repetition, Boolean or cold-family semantics, return iteration, target closure,
CT3 execution, or density estimate.

### 2026-07-16 node `[173]`: one component D1--D3 observation

Node `[173]` consumes node `[170]`'s actual component boundary input and
result. The reusable graph package independently computes the declared-order
BFS-tree shortest path in that component. Its observation-interface rank is
zero exactly on equality with this one computed path and one otherwise; it
does not generate, order, or scan a path family. The two literal capped
boundary degrees, two literal `Fin 13` offsets, connector length, thirteen
power-of-two target responses, and unique empty local response project to one
genuine `State (Fin 0)`. The result honestly retains
`MissingD4D7Reconstruction`.

Materializing this single state inspects exactly two ambient degree rows and
thirteen fixed target offsets, for `2*n + 13` visible checks and the linear
bound `15*(n+1)`. The theorem-independent transfer example executes the same
graph projection and verifies its exact boundary observations, missing D4--D7
residual, exact work, and linear bound.

The Chapter 1 boundary is exactly 92 green nodes among 174 active nodes and has
zero yellow nodes. Nodes `[160]`, `[164]`, `[174]`, and `[175]` remain
white. Node `[174]` is the dependency-ready cyclic component D1--D3 ledger
split downstream only of `[173]`; it remains unimplemented in this cycle.
Node `[175]` is the subsequent white D4--D7 reconstruction or coarse-repeat
consumer. Neither edge enters node `[164]`. Node `[173]` proves no state
sequence, repetition, D4--D7 reconstruction, CT3 compression, Boolean or
cold-family semantics, target closure, or density estimate.

### 2026-07-16 node `[174]`: cyclic component D1--D3 ledger split

Node `[174]` consumes a typed node-`[173]` residual and equality to the actual
node-`[173]` run, together with node `[170]`'s exact complete incident-stub
schedule. The retained node-`[173]` state is used exactly at the anchor row.
Every other row is computed by locally re-anchoring the node-`[170]` schedule,
whose successor remains the stored cyclic `List.next`. The reusable graph
runner applies finite code collision only to this observed row list. It returns
either two distinct rows with equal coarse `State (Fin 0)` values or a proof
that the schedule length is at most
`Qbase = 4^2 * 13^2 * 2^13`. The latter uses the proved state-cardinality
identity without enumerating the state universe.

The local work ledger charges the actual schedule, component restrictions, and
connector/BFS clauses and proves `visibleChecks ≤ 100 * localScale^4`. The
theorem-independent `InducedPathComponentD1D3Ledger` example executes the same
runner. Focused generic, transfer, and Erdős builds pass; the trust audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

The current Chapter 1 boundary is exactly 95 green nodes among 176 active nodes and
has zero yellow nodes. Node `[175]` remains the white D4--D7 reconstruction or
coarse-repeat consumer. The repeated branch supplies only equality of observed
coarse states, not full response equivalence or CT8 removal; the bounded branch
supplies no missing coordinates. Node `[174]` proves no CT3 compression,
Boolean or cold-family realization, target closure, return iteration,
termination, or density estimate, and it has no edge to node `[164]`.

### 2026-07-16 nodes `[22]`--`[24]`: exact routing and interface audit

The graph-owned alternative handoff from node `[21]` is now production code.
`P13Node21PartXIRoute` maps the exact CT12 packing list, retaining for every
window its classifier-produced thirteen-bit cold residual and computed
same-window node-`[159]` frontier. The four structural subledgers partition
exactly `p13` windows. No graph, completion, support, or context family is
enumerated. This does not substitute the actual-adjacency system for the
still-missing 91-coordinate completion responses, so nodes `[22]` and `[23]`
remain white.

The node-`[24]` boundary was strengthened after audit showed that its former
ceiling could be chosen tautologically as `p13`. It now requires the exact
finite density inequality
`118108581006 * U13 ≤ 1500000000 * |V(G)|`, as well as `p13 ≤ U13` and
the strict-quarter budget. Thus the type now names the manuscript density
claim honestly. There is still no inhabitant: the non-dyadic node-`[159]`
outputs lack an aggregate bounded-multiplicity terminal ledger. The long and
first-transition semantic consumers remain at nodes `[164]` and `[175]`, while
node `[171]` is the exact unconsumed all-inside token-pair residual.

### 2026-07-16 node `[177]`: finite attachment and germ-shape classifier

Node `[177]` consumes node `[144]`'s actual typed semantic trigger, including
the identical collision, two literal attachment maps, and the same two
canonical rooted germs. The reusable core decision scans exactly the declared
`WindowIndex × Fin 13 × Bool × PortRole` coordinates, of cardinality
`78*p13`. It returns the first actual predicate mismatch or proves complete
coordinatewise alignment. Only in the aligned branch does the graph package
inspect the already stored tree-path comparison, yielding exactly one of
left-prefix, right-prefix, root-divergence, or after-edge-divergence.

The five returned tags form an exact-selection CT10 profile: all five tags are
listed, precisely the computed tag is accepted, the public runner and verified
stage are retained, and the exhaustive trace is proved valid. The total work
is `234*p13 + 7 ≤ 234*n + 7`. The independent transfer example executes the
same core/graph/CT10 path. No ambient path, context, quotient, subgraph, graph,
coloring, or state universe is enumerated.

The Chapter 1 boundary is exactly 96 green nodes among 178 active nodes and
has zero yellow nodes. Node `[178]` is now the explicit white consumer that
must turn each exact classifier leaf into a sparse exit, CT3 response result,
decorated Type B handoff, or fixed-cap conclusion. Node `[177]` proves none of
those semantic consequences and does not prove the near-cubic spine.

### 2026-07-16 node `[164]`: first-nine observed-label refinement

Node `[164]` now consumes node `[163]` through a proof-carrying source that
stores equality with its actual forced-prefix run. The graph classifier maps
only the first nine exact prefix positions to their literal corridor vertices
and computes `(ambient degree mod 4, selected-packing membership)`. A local
collision scan retains two distinct actual occurrences with the same one of
eight labels; it never enumerates the label universe or the full `Qbase+1`
prefix.

The typed route gives CT10 exactly those two collided occurrences. Its three
classes are coarse label, compatible response contexts, and certified
removal; only the coarse row is populated, so the verified exhaustive trace
promotes the missing compatible-response layer. The combined work bound is
`144*(|V|+1)+9`. The independent framework example executes the same graph
and CT10 route, and the trust review reports only the standard Lean axioms.

The old full D4–D7 response-equivalence and CT8-removal claim is isolated at
new white node `[179]`, the sole downstream consumer of `[164]`. Node `[164]`
does not assert compatible-context completeness, response equivalence, CT8
removal, or a smaller object. The Chapter 1 boundary is now exactly 97 green
nodes among 178 active nodes and has zero yellow nodes.

### 2026-07-16 node `[175]`: D4--D7 availability and CT10 routing

Node `[175]` consumes node `[174]`'s exact generic result and its proved
agreement with the specialized P13 execution. A repeated coarse pair is
retained literally and CT10 promotes its first row as a missing refinement.
On the bounded branch, the graph runner scans only the actual duplicate-free
incident schedule and returns a reconstructed family or its first typed
missing D4--D7 row; that row is routed through CT10 on the identical
`ctx.toBranchContext`.

The route layer is generic over an arbitrary problem and branch context. The
non-Erdős transfer executes the repeated and bounded-first-missing branches,
and the combined graph/route work is at most `3*localScale`. No State,
response, context, graph, or ambient universe is enumerated. Full compatible
D4--D7 responses, CT8 removal, and certified-smaller-object semantics remain
white at node `[180]`.

The Chapter 1 boundary is exactly 98 green nodes among 179 active nodes and
has zero yellow nodes.

### 2026-07-16 nodes `[178]`--`[180]`: reviewed local semantic refinements

Three independently implemented and cross-reviewed consumers advance the
frontier without strengthening their inputs. Node `[178]` consumes every exact
node-`[177]` constructor, retains mismatch and prefix leaves, and extracts only
literal distinct incidences plus the local cubic/high separator split. Node
`[179]` consumes node `[164]`'s actual collided occurrences and promoted CT10
obligation, reading precisely their two full degree rows. Node `[180]`
consumes node `[175]`'s actual execution, eliminates the impossible complete
anchor reconstruction, and retains its exact missing D4–D7 witnesses.

All three use local clauses only. Their respective work bounds are
`|V|+1`, `2*|V|+1`, and one constructor inspection bounded by
`localScale+1`; no ambient response, context, state, graph, or universe family
is enumerated. Independent transfer fixtures and trust audits pass. The
stronger consumers are explicit white nodes `[181]`, `[182]`, and `[183]`.
The Chapter 1 boundary is exactly 101 green nodes among 182 active nodes and
has zero yellow nodes.

### 2026-07-16 nodes `[181]`--`[183]`: normalized local obligations

Node `[181]` converts only already retained cubic divergence incidences into
literal four-vertex cubic-star data and leaves high-degree branches as
`degree >= 4`; it performs zero new checks. Node `[182]` retains node `[180]`'s
dependent markers and emits fixed noduplicated D4--D7 obligation ledgers; its
actual computed output has eight slots on the coarse branch and four on the
bounded branch. Node `[183]` retains both node `[179]` degree constructors and
the CT10 `responseContexts` obligation, comparing adjacency only on the same
nine literal prefix coordinates.

Independent review repaired the node-`[182]` output budget and added concrete
aligned/mismatch transfer executions for node `[183]`. All focused builds and
trust audits pass. Stronger semantics remain white at nodes `[184]`, `[185]`,
and `[186]`. The Chapter 1 boundary is exactly 104 green nodes among 185 active
nodes and has zero yellow nodes.

### 2026-07-16 nodes `[184]`--`[186]`: literal local-clause projections

Node `[184]` consumes all seven constructors of node `[181]` exactly. Its
cubic leaves expose the stored switch boundary and support; its high leaves
retain the identical high-center ports, their cardinality, and the proved
degree lower bound. Node `[185]` consumes node `[182]`'s dependent ledgers,
focuses the literal D4 head, and retains exactly the D5--D7 tail. Node `[186]`
consumes node `[183]` and scans only positions 9--17, returning an inherited
mismatch, a second mismatch, or first-eighteen alignment while preserving the
node `[179]` degree residual and CT10 response-context obligation.

All three have independent transfer executions and cross-reviews. Their work
is bounded respectively by `|V|`, six actual tail slots, and eighteen local
adjacency checks. They do not enumerate an ambient graph, response, context,
state, or universe family and prove no downstream response or CT8 semantics.
Those stronger consumers remain white at nodes `[187]`, `[188]`, and `[189]`.
The Chapter 1 boundary is exactly 107 green nodes among 188 active nodes and
has zero yellow nodes.

### 2026-07-16 nodes `[187]`--`[189]`: reviewed pending obligations and local scans

Node `[187]` consumes node `[184]` exactly, retains every literal payload, and
maps its seven constructors to pending sparse-exit, fixed-cap, CT3, or Type B
obligation tags. The tags contain no certificate. Node `[188]` consumes each
actual node-`[185]` cursor and emits only a singleton D4 evaluation request,
retaining its dependent marker and exact D5--D7 tail. Node `[189]` preserves
both inherited mismatch constructors and otherwise scans only literal
positions 18--26, yielding a third mismatch or first-twenty-seven alignment.

Independent cross-review confirms exact predecessor provenance and payload
preservation. Work is bounded by one constructor inspection, two actual
request slots, and eighteen new local adjacency evaluations respectively.
No caller-supplied Boolean or ambient graph, response, context, state, or
universe enumeration occurs. Semantic producers remain white at nodes
`[190]`, `[191]`, and `[192]`. The Chapter 1 boundary is exactly 110 green
nodes among 191 active nodes and has zero yellow nodes.

### 2026-07-16 nodes `[190]`--`[192]`: first clauses and evaluator requirements

Node `[190]` consumes node `[187]` exactly. Its cubic leaves expose three
injective adjacent boundary incidences and its high leaves the first four
distinct declared ports and adjacent endpoints; mismatch and prefix evidence
passes unchanged. Node `[191]` retains every node-`[188]` request, marker, and
D5--D7 tail and exposes exactly the missing graph-local predicate and
predicate-provenance requirements. Node `[192]` preserves all three inherited
mismatches and otherwise scans only literal positions 27--35.

Independent cross-review confirms fixed local work bounds of four positions,
four actual requirement tags, and eighteen adjacency evaluations. No Boolean,
evaluator, strong semantic certificate, response equivalence, CT8 result, or
ambient enumeration is introduced. The next producers are white nodes
`[193]`, `[194]`, and `[195]`. The boundary is exactly 113 green nodes among
194 active nodes with zero yellow nodes.

### 2026-07-16 nodes `[193]`--`[195]` and root-reachable workflow audit

Nodes `[193]`--`[195]` are implemented as the terminal local residual
interfaces justified at the manuscript boundary. Node `[193]` retains the
exact node-`[190]` source and emits only its pairwise local-separator clause;
node `[194]` retains every node-`[191]` D4 request and records the missing
graph-derived evaluator construction; node `[195]` retains node `[192]`'s
three inherited mismatches or its exact first-thirty-six compatible-response
frontier. None of these nodes claims the absent semantic consumer.

The typed workflow was then audited independently from the displayed diagram.
Three implemented components were found to be orphaned: the whole-packing
node-`[21]` Part-XI route, the node-`[84]` local fan-mass endpoint, and the
node-`[144]` coarse-bottleneck chain. Exact composition links now connect them
respectively from the multi-scale curvature prefix, the Type B residual-center
ledger, and the homogeneous-pattern audit. Each target constructor consumes
the identical predecessor prefix. The regenerated artifact has 96 workflow
stages, 96 links, and all 96 stages reachable from `proof-slice.official`.
A frontend regression test enforces this root-reachability invariant.

The Chapter 1 boundary is exactly 116 green nodes among 194 active nodes with
zero yellow nodes. Independent repair audits keep nodes `[160]` and `[176]`
white: their current sketches still lack graph-owned all-window/gluing and
global Type B support-family producers, respectively. No Boolean cube,
ambient graph family, context universe, or caller-supplied support schedule is
enumerated.

### 2026-07-16 first non-Boolean producer units beyond the green boundary

Two producer units now advance the open contracts without changing any node
color. `FinitePrefixExtensionFamily` lifts the symbolic prefix runner to a
dependent finite family: it returns the first obstructed object with complete
earlier ledgers or complete ledgers for the whole family. The Erdős lift uses
the exact CT12 selected-window subtype and order, retains the unchanged
node-`[21]` prefix, runs the fixed 91-coordinate schedule, and proves the
visible envelope `91 * p13`. It does not construct the pointwise graph
completion machine and proves no realization or gluing theorem.

On the rigorous non-Boolean route toward node `[24]`, the fixed-skeleton entry
producer now traverses the graph-owned selected-window schedule once. For each
window it computes either the first strict-surplus position or the canonical
ambient-cubic external stub. It proves exact order and coverage, length
`p13`, the cubic counts 15 and 13, and a quadratic local-work bound. The next
required producer must consume these stubs through the fixed D4--D7
reconstruction/F2--F4 residual routing and bounded-multiplicity aggregation;
no density cap or quarter-budget statement is assumed.

The node-`[176]` and join-node audit also found that connected remainder
components are not Type B entries. No such helper was imported or retained as
node evidence. The first genuine Type B global producer must instead enumerate
the exact node-`[65]` ordinary and node-`[108]` decorated entry schedules with
dependent predecessor provenance before building grouped occurrences and the
coefficient-208 CT14 bridge. Consequently nodes `[76]`, `[85]`, `[160]`, and
`[176]` remain white.

### 2026-07-16 Part-I fixed-skeleton branch-excess producer

The paper's exact `15 - 2 = 13` step is now constructive rather than only
arithmetic. `Graph.InducedPathColdBranchExcess` enumerates the fifteen literal
external incidences of one ambient-cubic selected window, removes exactly its
first two transit stubs, and proves that the remaining thirteen stubs are
duplicate-free and owned by the same window. A graph-generic transfer example
executes this producer independently of the Erdős application.

`P13FixedSkeletonBranchExcessCorridors` filters the exact CT12 window order to
ambient-cubic windows and constructs thirteen literal sources per window. Its
deleted-edge-return F1/F4/F5 run is retained only as a provisional diagnostic:
it returns to the original window, makes F2/F3 empty, and treats high degree as
F4. It is not the paper's outside-component successor corridor and supplies no
node-status evidence.

`Graph.InducedPathBranchExcessComponentEntry` repairs the structural handoff.
For each literal source it performs one endpoint-membership decision and
returns either an exact `InducedPathComponentBoundarySchedule.Input` or a
typed cross-window residual. `P13FixedSkeletonComponentEntries` maps that
dichotomy over the complete thirteen-per-window schedule and proves a lossless
component/cross-window partition and a linear decision bound. On the component
branch it exposes the complete incident schedule, true cyclic successor,
same-component proof, and computed shortest component path. A graph-generic
non-Erdős transfer instantiates the same producer.

`P13FixedSkeletonComponentD1D3` consumes that exact two-ledger result. On each
component constructor it executes the graph-owned D1--D3 projection, retaining
the source token, two boundary degrees, two window offsets, connector length,
thirteen target-offset bits, and the typed missing-D4--D7 marker. Cross-window
constructors pass unchanged. The complete projection ledger has a proved
quadratic visible envelope and enumerates no response or context universe.

`Graph.InducedPathComponentD4` then constructs the first missing declared
clause as an actual finite family: one boundary-window role and one internal
length-two wedge of the stored active support, evaluated by the exact
`omegaTwo` relation on its three graph-derived attachment labels.
`P13FixedSkeletonComponentD4` maps that construction over every observed
component while retaining the exact D1--D3 source. The local scan has a proved
`4*n^3` envelope including wedge classification and response evaluation, a
non-Erdős transfer, and the standard Lean trust base.

The next genuine paper obligation is graph-owned D5--D7 on these exact
component observations and the complete initial-prefix
F1/F2/F3/F4/F5 consumer. Bounded overlap and the node-24 density certificate
are not invoked before that bound is proved. The exact outer
`P13PartIWindowDensityTriage` also computes certificate, density-overflow, or
quarter-obstruction leaves from node 21 without manufacturing either missing
inequality. Nodes `[22]`--`[24]` remain non-green.

The provisional deleted-edge-return verification ledger has the explicit
bound `n^2`:
each return support is a simple path of length at most `n`, while
`13 * card(cubic windows) ≤ 13 * p13 ≤ n`. The subsequent
`P13FixedSkeletonF5ScaleRouting` performs one local comparison on every
provisional F5 entry at the fixed `Q_base` threshold. It materializes no
fixed-state universe, but it is not connected to the corrected manuscript
corridor and is not counted as F5 implementation.

### 2026-07-16 direct cross-window handoff and local D7 support

The deleted-endpoint branch now has an exact consumer rather than a bare
membership residual. `Routes.InducedPathCrossWindowIncidencePair` recovers the
unique ambient-cubic selected-window slot containing the endpoint, proves that
its owner differs from the source window, and constructs the reverse external
incidence. The output retains two distinct cross-window tokens, their opposite
orientations, and equality of the underlying literal edge. The route uses the
stored endpoint-membership proof and packing disjointness; it performs no
owner-change path scan and no ambient window or context enumeration.
`P13FixedSkeletonCrossWindowIncidencePairs` maps this handoff over the complete
thirteen-per-window source schedule while passing component entries unchanged.

The D4 evaluator now also materializes the normalized two-boundary state and
proves exact boundary-degree, window-offset, target-response, and local D4
response projections. For D7, `Graph.InducedPathComponentD7` filters the
already graph-owned sparse-pair supports to those literally contained in the
component's active interface. `P13FixedSkeletonComponentD7Support` recomputes
that schedule on the identical minimal context and retains exact D4
provenance. This is a genuine D7 support schedule, not yet a D7 Boolean
evaluator: the existing sparse-pair response is context-indexed.

The manuscript and web companion now expose the maximal honest post-node
`[194]` handoff without adding a numbered diagram node. The exact node-`[194]`
marker is consumed by `P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation`;
its exhaustive theorem identifies the graph-owned `Omega_2` response on each
actual support wedge and preserves the remaining coordinate tail
`[D5, D6, D7]`. The visible work is bounded by `8 * n^3` in the coarse case
and `4 * n^3` in the bounded case. Boolean D7 semantics, compatible-context
responses, removal, and the smaller-object/CT8 conclusion remain open.

Independent D5 and D6 audits found no dependency-ready producer from the
component path alone. D5 first needs a proved Type A support and canonical
cubic-to-receiver trace family. D6 first needs a proved Type B assigned
support, fan-window/certificate data, candidate and overlap ledgers, and
proof-carrying handoff arms. Substituting the component BFS path for either
package would be branch leakage. Full framework and Erdős test builds pass;
the generated status remains honestly at 116 green nodes and zero yellow
nodes, with nodes `[22]`--`[24]` still white.

The first missing D5 prerequisite is now reusable rather than merely named.
`Graph.TypeACanonicalReceiverTrace.SupportProfile` packages an exact connected
Type A support, ambient cubicity, internal subcubicity, and internal
three-core-freeness. For every internal cubic vertex, the producer runs the
declared-order BFS in the induced support, selects the first low-degree vertex
in the first occupied layer, and retains the canonical tree trace. Lean proves
that the endpoint has internal degree at most two, every strict prefix vertex
has internal degree exactly three, the trace is a path, and it is shortest to
the receiver set. This scans only the supplied support and has a polynomial
work envelope. It does not yet manufacture the missing Type A support from a
component entry or claim the later port/channel/basin coordinates.

### 2026-07-16 nodes `[61]`--`[63]`: exact local split and Type A ancestry

The Type A trace prerequisite now has a same-context application route.
`TypeBEntryRouting.VerifiedNode61Residual` retains the exact sparse-surplus
predecessor, connected negative support, and a proof that every support vertex
belongs to the selected `P13` remainder. Node `[62]` scans only the literal
high-center finset of that support and exhaustively returns either an actual
degree-at-least-four witness or equality of that finset with the empty set.
The first result enters the existing node-`[64]` Type B handoff using the same
support; the second enters `TypeANode63Support`.

On the no-high branch Lean derives ambient degree exactly three from the
minimum-degree baseline, embeds the support into the exact remainder, proves
`P13`-freeness and ambient power-cycle avoidance, and invokes the sole HSS
theorem to obtain internal-three-core freeness. These results construct the
graph-owned Type A support profile and its finite canonical trace-incidence
schedule. A generic non-Erdős example validates the coordinate layer.

Node `[61]` is no longer allowed to preselect a negative cell in the CT
execution. `Graph.OrderedSupportComponents` computes the first-occurrence
component order of the literal remainder and proves connectivity, disjointness,
coverage, and a linear scan bound. `P13NegativeSupportLocalization` proves that
internal component degrees equal remainder degrees, expands the local charges
pointwise, sums them over the canonical partition, and bounds the true integer
charge by the upstream natural net numerator (including the truncated-
subtraction case). The genuine strict-quarter handoff therefore supplies a
negative total, and CT11 selects the first negative component. No component
schedule or negative support is a caller field. Nodes `[61]`--`[64]` now have a
complete typed implementation conditional only on the genuine node-`[24]`
predecessor, so they remain white until nodes `[22]`--`[24]` are closed. No
component family, graph universe, context universe, or Boolean state cube is
enumerated.

### 2026-07-16 per-window component/cross-window majority

`Core.LocalBinaryMajority` now owns the reusable lossless binary-list
partition and odd-majority runner. It filters only the supplied finite list,
proves that the two filtered lengths sum to the original length, and returns a
proof that one side of a list of length `2r+1` has at least `r+1` entries. A
non-Erdős five-entry fixture exercises the producer.

`P13FixedSkeletonWindowMajority` instantiates that runner separately for each
actual ambient-cubic selected window. It reconstructs the exact thirteen
branch-excess sources from `p13WindowBranchExcessCorridors`, executes the
existing component-entry route on each source, proves `A+X=13`, identifies the
complementary ledger exactly with the cross-window tag, and returns the
exhaustive alternative `7≤A` or `7≤X`. The visible universe is exactly the
thirteen entries of the supplied window. This local counting split does not
claim D5--D7 semantics, cross-window quantitative closure, or completion of
nodes `[22]`--`[24]`.

### 2026-07-16 cross-heavy oriented-incidence ledger

`Core.LocalInjectiveLedger` now owns the reusable aggregation step for an
explicit list of local schedules. Local label injectivity and label separation
between distinct indices imply a duplicate-free global label list; a proved
per-index lower bound sums over exactly the stored indices. A non-Erdős
two-block fixture proves the transfer independently.

`P13FixedSkeletonCrossHeavyLedger` filters the actual ambient-cubic selected
windows by the computed cross-heavy inequality and aggregates only their
actual cross-window branch-excess entries. The literal oriented window token
is injective within one window because the branch-excess stub list is
duplicate-free, and tokens from distinct windows are separated by their
stored owner coordinate. Consequently the complete oriented ledger is
duplicate-free and
`7 * card(cross-heavy windows) ≤ card(oriented cross incidences)`.

This is the earliest dependency-ready no-overcounting statement. The ledger
does not quotient orientations to unordered edges: that next step requires an
exact factor-two/reverse-closure theorem for the selected branch-excess
subschedule. It also supplies no response-preserving commuting gluing. Those
are the exact remaining inputs before the cross-heavy side can contribute to
node `[22]` or the later density closure, so nodes `[22]`--`[24]` remain white.

### 2026-07-16 exact reverse-closure split on the cross-heavy ledger

`Core.FiniteReverseClosure` scans one supplied duplicate-free item list and
classifies it without enlarging the universe. It retains either a proof that
every item has its declared reverse key in that same list or the first missing
item together with its clean-prefix certificate. On the proof-carrying closed
subledger only, actual unordered key pairs have fibres of size at most two, so
Lean proves `card(closed items) ≤ 2 * card(actual pair labels)`. A separate
non-Erdős fixture covers both the closed and first-missing outcomes.

`P13FixedSkeletonCrossHeavyReverseClosure` instantiates this scan on exactly
`p13CrossHeavyOrientedTokens`. Every token source is reconstructed from the
literal nested window/entry membership proofs, and its reverse token is the
existing cross-window incidence-pair route output. Thus the application now
returns the exhaustive split: all selected orientations are reverse-closed,
or a first concrete selected orientation is missing its reverse. The
factor-two theorem is deliberately asserted only for the filtered closed
subledger; it does not assume away the missing branch. The missing-reverse
residual is now consumed one local owner at a time. Its reverse-pair route
retains the exact destination-owner slot and local token. The generic
`Core.LocalPrefixTail` classifier splits membership in that owner's literal
fifteen-token order into the first two transit positions or the remaining
thirteen branch-excess positions. A non-cross-heavy destination owner is
rigorously routed to the component-heavy `7`-of-`13` branch. If the owner is
cross-heavy as well, Lean reconstructs the destination owner's canonical
branch-excess stub, corridor, and component-entry decision. The reverse
endpoint is a selected-window vertex and hence lies in the deleted support, so
the local decision is necessarily `crossWindow`; exact list membership then
places the reverse in `p13CrossHeavyOrientedTokens`. Thus the former selection-
mismatch constructor is contradictory. A genuinely missing reverse now has
only the transit or non-cross-heavy/component-heavy outcomes. The all-closed
branch still needs response-preserving commuting gluing, and the transit and
component-heavy residuals still need their later manuscript consumers.
Therefore this result does not close nodes `[22]`--`[24]` or change their
status.

`P13FixedSkeletonCrossHeavyMissingLedger` now lifts that resolved dichotomy
over exactly the filtered `missingItems` subledger. Each attached token keeps
its original missing-list membership, canonical source occurrence, proved
missing reverse, and resolved local outcome. Every non-transit item projects
to its exact destination owner together with the proof that this owner is not
cross-heavy and has at least seven component entries.

For transit items the ledger filters once more by the exact destination owner.
Equality of two reverse tokens forces equality of their opposite source tokens
by owner-slot uniqueness and selected-window position injectivity, so the
reverse-token labels of one fibre are duplicate-free. Every such label belongs
to the literal `take 2` of that owner's fifteen-token order. The reusable
`Core.LocalFiniteCapacity` transfer therefore proves that every destination-
owner transit fibre has cardinality at most two. Only the actual missing list,
owner fibre, and local two-token capacity list are inspected; no graph or
universe is enumerated. This aggregation does not implement the deliberately
open commuting/Boolean-realization branch.

The owner fibres now form an exact global partition. The reusable
`Core.LocalFibreCapacity` profile stores the transit-missing list, the literal
ambient-cubic owner order, the graph-computed owner map, and a local Boolean
owner equality backed by that finite enumeration's `DecidableEq`. Coverage is
proved because every retained destination owner belongs to this exact owner
order; disjointness is equality of the stored owner coordinate. Summing the
two-per-owner fibre bound gives
`card(transit missing) ≤ 2 * card(ambient-cubic windows)`. The constructor-
derived Boolean transit tag also gives a lossless transit/non-transit length
partition, and membership in the non-transit schedule still projects to the
exact non-cross-heavy component-heavy owner. No classical predicate cube,
ambient token universe, commuting response, or Boolean realization is used.

The ambient-cubic filtering loss is now connected to the same exact source
schedule. `p13_le_ambientCubic_add_totalSurplus` specializes the reusable
window-surplus injection to the complete CT12 packing, identifies its filtered
cardinality with `p13AmbientCubicWindows`, and proves
`p13 ≤ cubicWindows + totalSurplus`. Thus every discarded non-cubic window is
paid by a distinct graph-computed surplus unit; no asymptotic loss or caller
bound is assumed.

### 2026-07-16 first exact D6 subfamily

`Graph.TypeBFanCenterCoordinate` constructs the earliest dependency-ready D6
coordinates: the declared neighbor schedule of one proved high fan center,
with literal center--endpoint support, adjacency, exact degree cardinality,
and a linear work bound. `TypeBFanCenterCoordinates` consumes the exact
branch-tagged node-`[65]` input. The ordinary constructor uses node `[64]`'s
high-center witness, while the decorated constructor uses node `[66]`'s stored
handoff center. A non-Erdős transfer verifies the graph layer. This is not full
D6: fan-safe pairs, certificate labels, closed fan-window pairs, hybrid
incidences, candidate/overlap ledgers, and decorated-arm responses remain
separate exact-producer obligations.

### 2026-07-16 induced-core whole-port assignment

`Graph.InducedCoreFanAssignment` derives the assignment judgment rather than
accepting it from the application: an actual endpoint--shoulder carrier is
assigned exactly when it is a graph edge and both endpoints lie in the finite
node-`[64]` core. Its fixed-order classifier inspects the two literal
shoulders of one actual port and returns both assignment proofs, the first
missing assignment, or the second missing assignment after retaining the
first proof. `TypeBFanWholePortAssignment` instantiates the P13
window/remainder profile, retains both incidence ledgers, and turns a two-sided
success on an open port into the exact `FanClosedPort.FanClosed` input. No
assignment or certificate predicate is supplied by the caller.

### 2026-07-16 local compatible-pair and CT5 assembly

The already verified `Graph.HighCenterPort.VerifiedStage.dichotomy` supplies
either an existential compatible pair of actual open ports or the exact
degree-minus-two triangular bound. No second scan of an open-port Cartesian
square is performed. On the compatible branch the application proof-selects
the two witnesses from that retained existential and performs only the four
literal induced-core carrier decisions. `Graph.FanClosedPairAssembly`
generically combines two proved closed ports into the four-field
`AssignedPair` and verified constant-work CT5 stage, with a separate
non-Erdős transfer example.

`TypeBFanCompatiblePairAssignment` consumes the local CT10 dichotomy at the
exact node-`[64]` high center. It preserves the triangular result and every
first-missing carrier result. Only a compatible pair whose two ports both pass the
whole-port assignment classifier reaches the proof-carrying `AssignedPair`
and CT5-ready branch. Its visible work is the linear incident-port CT10
classification plus four carrier decisions. Fan certificates and marked labels
remain later availability obligations and are not assumed here.

The node-`[64]` connector now performs the manuscript's degree split before
the compatible-pair branch. Degree exactly four is retained as its own typed
handoff toward nodes `[78]`--`[80]`; only the proved degree-above-four branch
enters the node-`[69]` local dichotomy. Thus a degree-four compatible witness
cannot leak into the node-`[70]`/`[71]` chain.

### 2026-07-16 marked-fan certificate requirement frontier

`Graph.FanCertificateRequirement` identifies literal port zero as the first
label obligation in the actual high-center neighbour order. It performs no
checks and enumerates neither labels nor attachment maps. The application
`TypeBFanCertificateRequirement` exposes the exact legal-P13-label completion
type at that port and forwards all degree-four, triangular, and carrier-
assignment residuals unchanged. A CT5-ready compatible pair reaches a
`certificateRequired` constructor only. This is deliberately a white/request-
only frontier: it does not claim that a label is absent, does not assert an
availability dichotomy, and does not manufacture or assume a `MarkedFan`.

### 2026-07-16 node-64 degree-four ledger connector

`TypeBDegreeFourLedgerConnector` consumes only the exact degree-four residual
split from node `[64]`. It instantiates `Graph.DegreeFourFanLedger` with the
same center, deletion-criticality proof, literal degree equality, and the
induced-core carrier assignment already derived on this branch. CT14 therefore
scans exactly four actual ports and proves the full node-`[79]` closed-count,
deficit, sign, trace, totality, and polynomial ledger without importing the
later global `TypeBSupportScope`. A separate non-Erdős example verifies this
generic transfer.

The next node-`[80]` datum remains an honest
`CertificateMarkingRequirement`. Its future completion is a proof-carrying
decision: either an actual `MarkedFan` with center exactly `h`, or a proof that
no such marked fan exists. In particular, there is no trivially constructible
`Option.none` branch and absence is not inferred from failed construction. All degree-above-four routes,
including triangular, carrier-missing, and certificate-required branches, are
forwarded unchanged.

### 2026-07-16 exact Type A completion-port coordinates

`Graph.TypeACompletionPortCoordinate` implements the next dependency-ready
declared coordinate after the canonical receiver traces. It scans the proved
receiver subtype of the supplied Type A support and then only each receiver's
actual ordered neighbor list, whose length is exactly three by ambient
cubicity, filtering the endpoints outside that same support. Every coordinate
therefore retains the literal receiver, outside endpoint, ambient adjacency,
internal receiver-degree bound, ambient degree three, and exact oriented-port
identity. Its primitive-check ledger charges one receiver test per support
vertex and three actual-neighbour tests per retained receiver, hence at most
four checks per support vertex and a linear bound; it enumerates no vertex-pair, path, support, context, state, or graph
universe. A separate non-Erdős framework example checks the shared API.

`TypeACompletionPortCoordinates` is the thin Erdős instantiation. It consumes
the proof-carrying `TypeANode63Support.VerifiedNode63Residual` directly and
transports both endpoints through its exact `profile_support` equality back to
the node-`[61]` support. Anchored-return existence, first-entry channels,
connector lengths, theta constraints, and silent-basin/carrier data require
later proof-carrying producers and are not asserted by this coordinate stage.
No diagram node changes status.

### 2026-07-16 anchored returns through exact Type A ports

`Graph.TypeAAnchoredReturnCoordinate` is the next manuscript producer. For one
exact completion-port incidence it consumes the proved non-bridge judgment and
uses Mathlib's reachability-to-simple-path theorem to select a path from the
outside endpoint back to the receiver in the graph with that port edge
deleted. The retained result is therefore exactly an anchored return: its
endpoint types, simplicity, and port-edge avoidance are Lean theorems. This
uses proof choice on a proved existential and performs no walk enumeration or
additional finite scan. A separate non-Erdős example consumes the same public
producer.

`TypeAAnchoredReturnCoordinates` constructs the producer from the already
verified CT2 theorem `dart_not_bridge` for every port in the exact node-`[63]`
schedule. Thus anchored-return existence is not a caller premise and every
return remains indexed by the node-`[61]` support and its node-`[63]` profile.
First-entry receiver selection and internal receiver-entry channel extraction
are the next local producers; they are not asserted here. No diagram node
changes status.

### 2026-07-16 first-entry receiver on an anchored Type A return

`Graph.TypeAFirstEntryCoordinate` scans only the stored support list of one
already selected anchored return, in traversal order. The proof-carrying first
hit retains the exact clean outside prefix, its last vertex as the predecessor,
and the literal predecessor--entry edge. The terminal receiver proves that the
scan cannot return absence. Since the predecessor is outside the Type A support
but adjacent to the first entry, while every support vertex has ambient degree
three, a strict neighbor-set cardinality argument proves that the first entry
has induced degree at most two. This is the full local content of
`lem:typeA-first-entry`; no path or return family is enumerated.

`TypeAFirstEntryCoordinates` applies the producer to the exact node-`[63]`
anchored return and transports the clean-prefix predecessor outside the
node-`[61]` support. Internal receiver-entry channel extraction is the next
local producer and is not assumed here. No diagram node changes status.

### 2026-07-16 Type A degree-two entry budget

`Graph.TypeAEntryBudgetCoordinate` proves the exact local content of
`lem:typeA-entry-budget`. It partitions the three actual ambient incidences of
each receiver into internal incidences and completion ports, proving that a
degree-two receiver has exactly one port. For an arbitrary proof-supplied
anchored return, the first-entry edge is converted into an exact coordinate in
the already constructed completion-port schedule. If its receiver were the
terminal receiver, port uniqueness would identify it with the deleted port,
contradicting adjacency in the port-edge-deleted return graph.

The family of all distinct first-entry edges is represented as a logical
subset of the existing local coordinate schedule; anchored returns and paths
are not enumerated. Its cardinality is bounded by the sum, over nonterminal
receivers, of the exact outside-incidence count, and this count is proved equal
to `3 - d_X(r)`, the manuscript quantity `q(r)`. The entry-budget layer adds
zero primitive checks to the earlier receiver/actual-neighbour schedule, so
the combined visible work remains at most four checks per ambient vertex.
`TypeAEntryBudgetCoordinates` consumes the exact node-`[63]` profile, anchored
return, and first-entry producers; the framework example provides a separate
non-Erdős transfer. No diagram node changes status.

### 2026-07-16 Type A connector and channel spectrum

`Graph.TypeAReceiverEntryChannel` extracts the manuscript connector `Γ` by
taking the prefix of the already stored anchored return through its computed
first support hit. Its support is proved exactly equal to
`hit.before ++ [entry]`; hence every nonterminal connector vertex is outside
the Type A support. A receiver-entry channel is a proof-carrying simple path
in the induced support graph. The framework maps such a channel into the
literal port-edge-deleted graph, proves that it avoids the deleted edge, and
proves by support separation that `Γ ∘ Q` is simple and has length
`g(Γ) + |Q|`. The semantic spectrum contains exactly the lengths represented
by supplied channels. Extraction and assembly perform zero new graph or
target-predicate checks. Extracting `Γ` does traverse the stored clean prefix
once: the explicit counter is `hit.before.length + 1`, proved at most the
stored return support length and at most the ambient vertex count. The
framework example exercises the same graph theorem and traversal bound
independently of the Erdős target.

`TypeAReceiverEntryChannels` consumes the exact node-`[61]` support,
node-`[63]` profile, completion port, stored anchored return, and computed
first entry. For every supplied channel, the assembled return and the
minimal-counterexample target-avoidance field prove
`g(Γ) + |Q| ∉ MersenneSet`, the first assertion of
`lem:typeA-spectral-pressure`. Its interval consequence is stated using
integer endpoint inequalities, so the manuscript band
`[μ-b, μ-a] ∩ ℤ_{≥1}` is not weakened by natural-number subtraction. No path
or channel family is enumerated, and no diagram node changes status.

### 2026-07-16 raw Type A continuation-germ prerequisite

`Core.RootedPathFamily` and `Graph.TypeADeclaredContinuationCoordinate`
formalize only the raw content needed before
`def:typeA-continuation-classes`.  Each supplied coordinate retains its actual
anchored return, computed first entry, extracted connector, internal channel,
finite declared support, declared value, and boundary-fibre image.  The family
runner is an ordinary executable definition that scans the supplied connector
list against its first connector and keeps the least observed branch index.
Its separator output contains the exact two coordinates, common prefix and
tails beginning at the two distinct next incidences, outside separator vertex, distinct next
incidences with deleted-graph and ambient adjacency, and a theorem that no
family coordinate branches earlier.  The public certificate also retains the
exact identity of its right coordinate with the family anchor and exports the
corresponding selected-pair and arbitrary-family-pair no-earlier theorems, so
the anchor-relative global proof cannot be attached to an unrelated right
coordinate.  The uniform output proves exact
connector coincidence and same-fibre identification.  The scan performs at
most the total stored connector-tail length in primitive equality checks (and
therefore at most `4L` for four tails of length at most `L`); it enumerates no
pair family, path, channel, context, state, or graph universe.  A separate
non-Erdős framework fixture checks the same public classifier and work bound.

There is intentionally no Erdős wrapper at this point: the actual D2 declared
response semantics and the proof-carrying four-return residual have not yet
been constructed.  No absorption, survival, CT3, or node-`[107]` conclusion is
asserted, and no diagram node changes status.

### 2026-07-16 typed nodes `[160]`, `[22]`--`[24]` handoff

Part I now records the manuscript's directed dichotomy at node `[160]` without
pretending to derive Boolean realization from the 91-row count.  The positive
constructor carries finite local completion states interpreted as actual
finite graphs on the fixed vertex type, exact selected-window embeddings,
local-support preservation, minimum degree, target avoidance, and response
bits computed from node `[21]`'s barrier relation. It proves realization of
every supplied 91-coordinate assignment, finite graph-owned global states,
support-commuting gluing, and exact restriction/recovery laws on the same
selected windows.  The open
constructor carries the exact negation of nonemptiness of that package and
names the three downstream producers still owed: local completion states,
simultaneous response realization, and commuting cross-window gluing.  The
split is proof-level and enumerates no state, assignment, Boolean cube, path,
graph, or context universe.

Only the realized constructor is an input to node `[22]`; the open constructor
remains at node `[160]` and cannot leak into either density successor.

Node `[22]` consumes that exact handoff and performs the manuscript's finite
packing-density dichotomy.  Its strict constructor is node `[23]`, which
retains the exact reverse cross-multiplied inequality and the open entropy
terminal consumer.  Its complementary constructor is node `[24]`, which
retains the exact packing ceiling and window-only cap and explicitly names
the normalized high-entropy refinement
`116808581006 * p13 ≤ 1400000000 * n` as a later requirement.  Both
constructors store the unchanged node-`[160]` handoff, so neither can bypass
the realization/gluing frontier.

Independent review also removed an unjustified `Nodup` requirement from the
raw Type A continuation-coordinate family: the paper supplies distinct routed
load occurrences, not necessarily distinct projected D2 tuples.  The
classifier never used coordinate-level distinctness.

The regenerated Chapter 1 descriptor has exactly 120 green nodes among 194
active nodes and zero yellow nodes.  Focused Erdős tests, the web export, and
the raw-to-compiled descriptor pipeline pass.

### 2026-07-16 repaired node `[48]` finite curvature/product split

Node `[48]` now follows the repaired Part-IV manuscript responsibility rather
than identifying CT15 full rank with simultaneous Boolean realization.  From
the exact node-`[24]` packing cap and the same-context node-`[47]` coordinate
ledger, `P13ForcedCurvatureCost` proves the finite ordinary and high-entropy
wedge inequalities with the retained total-surplus error.  No asymptotic
`o(|R|)` term is introduced without a fixed authored scale certificate.

The product-cost successor requires actual graph-completion contexts,
injectivity of their semantic interpretation, and an injective code into the
exact labelled baseline-skeleton count.  A Core-owned conditional-fibre
ledger filters only one supplied local state list along the declared
coordinate order and telescopes the exact `543958/111286` inequalities.  Its
non-Erdős transfer is the textbook triangle-free cycle `C₅`, using actual
neighbourhood and common-neighbourhood fibres and the Mantel theorem on the
same graph.

The exhaustive node-`[48]` output has a realized constructor, which alone may
feed node `[49]`, and an open realization requirement.  The open constructor
has a typed same-context consumer into the node-`[55]`/`[56]` route, but only
after the independent quarter-budget predicate is proved; it manufactures no
entropy or budget assertion.  The TeX diagram and corollary, Lean tests,
WebExport declaration index, and compiled descriptor are synchronized.  The
regenerated Chapter 1 descriptor has exactly 121 green nodes among 194 active
nodes and zero yellow nodes.

### 2026-07-16 node `[49]` finite realized-state entropy

Node `[49]` consumes exactly node `[48]`'s realized conditional-fibre payload.
It neither widens that family to all remainder graphs nor enumerates graphs,
subsets, contexts, assignments, or Boolean cubes. The Core-owned profile
defines the exact supplied count `N_R`, its executable `Nat.log2` numerator,
and the literal real normalization `Real.logb 2 N_R / |R|`; the floor theorem
identifies the executable numerator with the natural floor of the real
logarithm. The Erdős contract retains the unchanged predecessor, proves
`N_R > 0` from the terminal nonempty fibre, and derives the labelled-skeleton
capacity from node `[48]`'s actual edge-set encoding.

The bookkeeping performs zero semantic predicate calls. Length, logarithm,
and quotient formation are separately bounded by `2*N_R + 1` local
list/arithmetic steps. The non-Erdős Mantel transfer instantiates the same
contract on the five actual vertices of `C₅`, including its real entropy and
work bounds. Independent review verified the TeX--Lean--Web mapping and sole
standard Lean trust. The regenerated Chapter 1 descriptor has exactly 122
green nodes among 194 active nodes and zero yellow nodes.

### 2026-07-16 node `[50]` exact entropy-scale split

Node `[50]` consumes the exact dependent node-`[49]` proof and performs the
paper's high/low entropy threshold in denominator-free form:
`n^|R| ≤ N_R^10` or `N_R^10 < n^|R|`. Both constructors retain the identical
verified node-`[49]` payload. The Core-owned runner makes exactly one natural
power comparison and enumerates no graph, state, support, subset, context,
function, assignment, or Boolean universe.

The non-Erdős transfer uses the actual Mantel `C₅`: its five supplied vertex
states exercise the upper branch, while the actual degree-two neighborhood at
vertex zero exercises the strict lower branch. The manuscript definition and
diagram, Lean endpoint, Web declaration group, and generated descriptor agree.
Independent review found only standard Lean trust. The regenerated Chapter 1
descriptor has exactly 123 green nodes among 194 active nodes and zero yellow
nodes.

### 2026-07-16 node `[51]` high-power remainder bits

Node `[51]` is the narrow arithmetic successor of node `[50]`'s actual high
constructor. The total route pattern-matches the stored node-`[50]` outcome:
the high side retains the exact node-`[49]` and node-`[50]` predecessors and
derives `(|R|/10) * log₂ n ≤ log₂ N_R`; the strict low side is returned
unchanged for its separate consumer. No normalized division by `|R|`, joint
window/remainder injection, or node-`[52]` entropy cap is asserted.

Core owns the reusable passage from a natural power inequality to the weighted
real-log budget, using node-`[49]`'s positive state count. The concrete Mantel
`C₅` upper branch consumes that same theorem. The transfer performs no finite
scan and enumerates no graph, state, subset, context, function, assignment, or
Boolean universe. Independent review verified the TeX--Lean--Web mapping,
declaration coverage, and standard Lean trust. The regenerated Chapter 1
descriptor has exactly 124 green nodes among 194 active nodes and zero yellow
nodes.

### 2026-07-16 node `[52]` joint window--remainder accounting frontier

Node `[52]` consumes the exact node-`[51]` high-power constructor and preserves
its dependent node-`[49]` and node-`[50]` provenance. Its realized constructor
uses node-`[24]`'s actual `LocalCompletion`, `GlobalCompletion`, and `glue`,
node-`[48]`'s exact realized state schedule, recovery laws for both coordinates,
and an injective encoding into the literal `P13BaselineSkeleton`. The
Core-owned `FiniteJointCapacity.Profile.left_mul_right_le_codeCard` derives the
product-capacity inequality without materializing or scanning the Cartesian
product.

The exhaustive alternative is an exact open requirement naming the missing
multiscale window states, joint window--remainder commutation, injective
baseline encoding, and finite-cap arithmetic. Its node-`[55]` handoff consumes
an independently proved same-context `P13QuarterNetBudget`; it manufactures no
budget, high-entropy cap, or node-`[54]` contradiction. The non-Erdős Mantel
transfer applies the same Core profile to the five vertices and two incidence
orientations of the actual triangle-free cycle `C₅`, encoded by its ten
darts. Focused Core, Mantel, Erdős Tests/WebExport, and LaTeX builds pass.
Independent review found no admissions, unsafe declarations, external axioms,
or nonlocal enumeration. The regenerated Chapter 1 descriptor has exactly 125
green nodes among 194 active nodes and zero yellow nodes, with all 1267
displayed declarations explained.

### 2026-07-16 node `[53]` exact low-entropy forced-cost fit

Node `[53]` is constructed only from node `[50]`'s actual strict-low
constructor. The route retains the exact node-`[49]` outcome payload, its
equality to the verified predecessor, the strict power inequality, and the
equality identifying the stored node-`[50]` outcome. The node-`[48]`
conditional-fibre ledger and its nonempty terminal fibre prove
`A ≤ B*N_R`, where `A = 543958^|Ω|` and `B = 111286^|Ω|` use the
literal curvature-coordinate schedule. The Core-owned
`FinitePoweredBudgetTransfer.Profile.forced_pow_lt_flat_pow_mul_upper` then
combines this with `N_R^10 < U` to prove `A^10 < B^10*U` symbolically.

Consequently the printed reverse small-budget edge is impossible on this exact
incoming branch. The surviving large-budget payload exposes only a function
that consumes an independently proved same-context `P13QuarterNetBudget`; it
does not manufacture node `[55]`, node `[56]`, or a high-entropy node-`[54]`
closure. The non-Erdős transfer uses the same Core profile on the actual five
vertices and ten darts of the Mantel cycle `C₅`. Focused Core, Mantel,
Erdős Tests/WebExport, and LaTeX builds pass. Independent review found only
standard Lean trust and no admissions, unsafe declarations, evaluated huge
powers, or ambient enumeration. The regenerated Chapter 1 descriptor has
exactly 126 green nodes among 194 active nodes and zero yellow nodes, with all
1283 displayed declarations explained.

### 2026-07-16 node `[195]` exact long-prefix response handoff

The post-frontier repair converts each of node `[195]`'s four literal
nine-coordinate mismatch constructors into an actual graph-response
separator. The reusable graph profile uses exactly the already scanned 36
local corridor coordinates, at offsets `0`, `9`, `18`, and `27`, and proves
the corresponding adjacency responses differ. It performs one constructor
inspection and enumerates no graph, state, support, context, assignment, or
Boolean universe.

The fully aligned constructor remains an explicit typed requirement rather
than a claimed CT8 removal. It records precisely the two missing producers:
complete D4--D7 response semantics on the same local data and an exact-pair
certified reduction for the correct full-degree-plus-marked-bit exact type.
The prospective 73 checks are reserved for that future CT8 execution and are
not charged as current work. Lean, TeX, and Web metadata agree; focused
builds and independent review pass. The regenerated descriptor remains at
exactly 126 green nodes among 194 active nodes and zero yellow nodes, with all
1295 displayed declarations explained.

### 2026-07-16 post-frontier exact-type and D7 response connectors

The aligned node-`[195]` leaf now inspects its retained node-`[179]` degree
constructor before any CT8 use. A congruent nonzero degree gap proves the full
degree-and-marked exact types differ and exits the repetition route. Exact
degree, together with the retained marked-bit equality, proves equality of
the full exact type and constructs the ordered repeated pair on the literal
two-occurrence sequence. This gate performs one constructor inspection; it
does not claim complete D4--D7 semantics, removal, or CT8 execution.

On the short component cone, D7 support enumeration now retains D7 in the
pending tail. The graph-owned response restriction uses exactly that finite
coordinate schedule and the existing sparse-pair support, but leaves the
outside gluing context universally supplied. It proves literal supported-piece
and pointwise sparse-pair-response provenance for every supplied context,
without choosing or enumerating contexts or collapsing the response to a
context-free Boolean. Consequently D7 remains pending until a compatible-
response bridge is proved. The current generated descriptor remains at 126
green nodes and zero yellow nodes, with all 1308 displayed declarations
explained.
