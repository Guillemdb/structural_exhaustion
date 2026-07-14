# Erdős Problem 64 implementation state

This ledger records the Lean-checked proof content in
`examples/erdos_64_eg` as of 2026-07-14.

The theorem-bearing endpoint is
`Erdos64EG.Internal.exists_verifiedTypeBResolutionPrefix`:

```lean
(object : Object V) → Baseline object → ¬ Target object →
  ∃ ctx : Core.MinimalCounterexampleContext
      packedStaticInput.problem packedStaticInput.Target,
    packedStaticInput.problem.rank ctx.G ≤
        packedStaticInput.problem.rank
          (Graph.PackedFiniteObject.pack object) ∧
      VerifiedTypeBResolutionPrefix ctx
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
- the CT6 ordered surplus stage: one scan of the declared vertex order,
  a first-failure predicate for a non-cubic neighbour of a high centre,
  deletion-critical closure of that failure branch, the exact
  `Σ_v (d(v)-3)` active ledger, and a dependent excess-slot family of the
  same cardinality.
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
| `lem:sparse-excess-port-extraction`, cubic-endpoint clause of `lem:sparse-port-activation`, nodes `[127]`–`[128]` | `VerifiedP13LabelAlgebraPrefix` and deletion criticality on the identical selected packed graph | CT6 ordered activity profile through `Graph.SurplusPortActivity` | Exact active-ledger terminal and trace; first-failure semantics for the first high centre with a non-cubic neighbour; deletion-critical exclusion of every failure; exact `Σ_v(d(v)-3)` ledger; excess-slot cardinality; composed `VerifiedSparseSurplusPrefix` | One failure test per declared vertex and at most `|V|²` primitive adjacency/degree tests; no enumeration of paths, subgraphs, graphs, or attachment tables |
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

The next dependency-ready manuscript frontier is the decorated-handoff and
residual-core maximality transition, together with support connectivity and
the window-stub plus replacement/delocalization clauses of global-local
reflection. After that comes the fan-mass summation and the remainder of the
non-near-cubic surplus branch at nodes `[19]`–`[20]`, including the
return/suppression support in node `[128]`, node `[129]`'s baseline, and the
pair-response/free-blocked semantics following the now-verified pair
availability split at node `[130]`, through expanded nodes `[131]`–`[144]`.
Node `[21]` is reached only after the no-surplus branch of that routing. The
density-dependent assertion that `R` is large at nodes `[25]`–`[26]` remains
downstream and is not claimed by the packing or label-algebra stages.

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

## Independent transfer

The independent transfer is
`EvenCycleExample.CT14HighCenterDeletionCharge`. It instantiates the same
`Graph.HighCenterDeletionCharge.Profile` on the textbook complete bipartite
graph `K₃,₄`: the three degree-four vertices are the complete high-center
set, the four degree-three vertices form the retained edgeless graph, and
internal-three-core-freeness is proved directly without the external HSS
theorem. The theorem
`ConcreteK34.highCenterDeletion_deficit_bound` is the exact generic
`21 * assignedSurplus + receiverOverload` conclusion.

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

## Validation

The following checks pass on 2026-07-14 for the post-ledger review:

```text
make lint
  OK: CT1–CT17 expose only automation-first canonical APIs

make schemas generate
  Framework build completed successfully (3293 jobs)
  Even-cycle build completed successfully (3202 jobs)
  Erdős build completed successfully (3224 jobs)
  Greedy-coloring build completed successfully (1303 jobs)
  Mantel build completed successfully (3080 jobs)
  Rendered 4 compiled Lean examples
  Rendered 124 node, 37 residual, 9 route, and 51 tactic-level schemas
  Rendered 17 tactic projections and 9 generated routes

python3 tools/verify_lean.py
  Kernel checked 17 automation-first tactics, 124 nodes, 108 typed edges,
  37 residual kinds, 9 routes, and 4 compiled examples

python3 tools/validate_repository.py
  OK: 17 automation-first Lean tactics, 124 nodes, 108 typed edges,
  37 residual kinds, 9 generated routes, 0 manual node obligations

make web-frontend-test
  12 test files and 23 tests passed; typecheck and production build passed

latexmk -pdf -interaction=nonstopmode -halt-on-error erdos_64_proof.tex
  passed in an isolated output directory

git diff --check
  passed
```

The Python regression suite was not run in this environment: system `pytest`
is unavailable, and downloading it from PyPI was disallowed by the managed
sandbox. The Lean kernel, compiled catalog, repository validator, frontend,
and manuscript checks above are complete.
