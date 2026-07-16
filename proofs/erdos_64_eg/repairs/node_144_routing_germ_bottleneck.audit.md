# Red-team audit: node [144] routing-germ bottleneck

## Baseline

- Repair sketch: `proofs/erdos_64_eg/repairs/node_144_routing_germ_bottleneck.tex`
- Original manuscript baseline/hash: `59ca045186cd45af9b34cacad71fcb91fad2fa7b8b78628d9691f8d7ffb287eb`
- Failed node and claim: node `[144]`; the claimed obstruction to a fixed routing-label bottleneck and the resulting fixed homogeneous cap.
- Methodology consulted: external types and legal labels; CT7 and CT8 contracts; typed payload inventory; repair protocol levels 2--4; locally-testable-target scope condition.
- Lean contracts consulted: `Core.GreedyMatchingStar`, `Graph.SurplusHomogeneousPattern`, `Graph.SurplusPairResponse`, CT7, CT8, and the compiled route registry.
- Current verdict: **FAIL**.

The path-response lemma in the sketch is correct as a statement about unrestricted two-terminal paths. It does **not** establish the claimed obstruction for the exact node-`[144]` residual.

## Provenance matrix

| Used fact | Producer | Earlier on this path? | Independent of defect? | Verdict |
|---|---|---:|---:|---|
| Exact overloaded token--role fibre and unique class route | nodes `[137]`, `[139]`, `[141]`; `VerifiedCoupledClassOverloadPrefix` | yes | yes | admissible |
| Literal matching or star inside that fibre | nodes `[140]`, `[142]`, `[143]`; `Graph.SurplusHomogeneousPattern.Audit` | yes | yes | admissible |
| Exact free-pair supports and retained shortest connector | node `[130]`; `Graph.SurplusPairResponse` | only on the free-pair subtype | yes | admissible only on that subtype |
| Canonical first blocker | node `[130]`; `Graph.SurplusPairResponse.canonicalBlocker` | only on the blocked subtype | yes | admissible, but no node-`[144]` routing support has yet been built |
| Arbitrary two-terminal paths `X_a` and contexts `K_d` | repair sketch | no | no | **not derived from the frozen branch state** |
| Same token, role, local flags, and boundary profile for all `X_a` | asserted informally in the sketch | no | no | **unproved compatibility assertion** |
| Uniformly unbounded routing-label alphabet | repair sketch | no | no | **not proved**; omitted path length creates collisions, not additional label values |

## Quantifier attack

| Claim | Literal quantified form | Smallest countermodel attempted | Result |
|---|---|---|---|
| Unrestricted path responses have infinite context index | for all `a<b`, some `d` separates `a` and `b` for the power-of-two cycle predicate | `d=2^k-a` | **valid** |
| The node-`[144]` routing label must decode response in every compatible outside context | equality of the manuscript label implies equality of all external responses | unrestricted `X_a,K_d` | **wrong target**: the manuscript uses label equality to select two edges, then explicitly analyzes their actual germs and context/quotient failures |
| Finiteness of each graph-dependent label set fails to give a uniform cap | no graph-independent bound exists for the actual listed label coordinates | path length is unbounded | **not established**: path length is not a listed coordinate; the sketch does not exhibit any listed coordinate with unbounded range on the exact branch |
| The unrestricted path countermodel is compatible with node `[144]` | for each `a`, realize `X_a` as one selected pair in a common exact token--role fibre of a minimum-degree-three target-avoiding sparse-exit survivor | bare degree-two paths | **fails**: no host graph, activation data, token equality, role equality, sparse-exit survival, or canonical-support realization is supplied |
| Exact-type injection gives a smaller representative | equal finite response implies a `Core.SmallerObject` preserving baseline and target avoidance | none | **fails**: neither the sketch nor CT8 constructs the required certified reduction |

Injection/surjection, pairwise/simultaneous realization, rank/Boolean-cube, and representative-existence checks were all applied. The central defect is a quantifier/domain substitution: an unrestricted context-index theorem is presented as an obstruction for a much narrower typed residual without realizing that residual.

## Branch and invariant audit

- Positive-side payment/account: a fixed coarse routing label may still pigeonhole two pattern edges if every listed coordinate is proved to have a fixed finite range.
- Negative-side bounded witness/consumer: compare the two **actual** canonical germs and return `parallel`, `cubic first separator`, or `high first separator`; refine unsafe cases by the first failed sparse-exit/Type-B trigger field.
- Measurability: the common-prefix relation and first separator are computable on two supplied finite paths. They do not require an all-context external type or a bound on path length.
- Ladder legality: this is a level-2 structural refinement, with a possible level-3 payload registration if a new germ-comparison handoff is needed.
- Cross-branch leakage found: the sketch does not itself leak the near-cubic conclusion backward, but its countermodel imports arbitrary pieces not constructed on the branch.
- Theorem weakened or assumption added: none in the source manuscript; the repair sketch instead overstates what its countermodel proves.

### Finer finite invariant attempted

The following refinement avoids the infinite-index argument without pretending that a coarse label is an exact external type:

1. Define the routing label as the fixed product of the already listed finite local coordinates: total role, token subtype, endpoint orientation, local open/triangular status, germ terminal role, bounded-port boundary profile, bounded `P13` entries, and the suppressed-chord/free-anchor flag.
2. Prove a graph-independent cardinal bound for that product coordinate by coordinate.
3. Use a repeated label only to select two actual edges.
4. Construct their exact finite routing supports and deterministic germs.
5. Classify the pair by the finite relation `parallel | cubicSeparator | highSeparator`.
6. On `parallel`, construct either a concrete distinguishing-context payload or a proof-carrying certified reduction. On a separator, classify the first failed switch/fan-safety field and route it; only the all-fields-safe high branch constructs the decorated Type-B handoff.

This refinement does not encode arbitrary path response in the label. Its state space is fixed because path **relation**, rather than exact path length, is the post-pigeonhole invariant. It is not yet a proof of node `[144]`: the parallel certified-reduction theorem and complete Type-B trigger remain missing. It does disprove the sketch's claim that the infinite path-context index is already a methodology-level obstruction.

## CT obligations

| CT instance | Trigger | Unfilled schema | Payload/consumer mismatch | Verdict |
|---|---|---|---|---|
| Proposed CT8 on routing labels | ordered pattern states, finite exact-type alphabet, finite response contexts, total `remove` | no proof that the coarse label is an exact external type in the methodology sense; no semantically valid removal | Lean CT8 requires `Input.remove : State -> State -> SmallerObject` before response comparison and does not prove baseline/target preservation | reject current worksheet |
| CT7 on the parallel pair | bounded same-interface pair and finite complete context generator | generator completeness for every target-relevant compatible context | no such generator is constructed | unavailable as stated |
| CT9-to-CT7 registered route | capacity-one CT9 overload | current source is a classwise overload followed by greedy pattern extraction | route requires a capacity-one theorem and extracts the overload pair directly | not applicable |
| CT3 distinguishing-context consumer | two exact boundaried pieces and concrete separating context | pieces/interfaces and context payload absent | no compiled node-`[144]` producer route | expressible but unimplemented |
| CT10 finite local refinement | explicit germ relation/failed-field table | exact local semantics and every outgoing payload | no direct registered predecessor route required; ordinary composition is possible | viable design candidate, not discharged |
| CT17 long-germ route | bounded offset family and compatibility data | one long germ supplies neither | trigger mismatch | correctly rejected |

There is no registered CT8 route in the compiled catalog. The only relevant registered route is capacity-one CT9 to CT7, which does not match the current classwise-overload/pattern source.

## Reused closed branches

| Handoff | Exact trigger proved | State transported | Consumer dependency cone independent? | Cycle measure | Verdict |
|---|---:|---:|---:|---:|---|
| Parallel distinction to CT3/sparse exit | no | no | not audited because payload absent | n/a | blocking |
| Parallel equality to minimality C2 | no certified reduction | no | n/a | strict rank decrease would be required | blocking |
| Cubic separator to sparse switch exits | no exact failed-field classifier | no | not yet shown | n/a | blocking |
| High separator to Type-B ledger | no decorated-envelope trigger | no | Type-B mass must not depend back on node `[144]`'s spine conclusion | n/a | blocking |

## Leaf totality

| Leaf | C1--C5 or typed consumer | Exact proof/certificate | Practical checker | Verdict |
|---|---|---|---|---|
| No repeated fixed routing label | bounded-cap certificate feeding the existing classwise accounting | absent until the uniform product bound is proved | linear label scan | open |
| Parallel, distinguished | CT3 or named sparse exit | absent | local once context supplied | blocking |
| Parallel, equal | C2 | certified smaller baseline target-avoiding object absent | constant after certificate | blocking |
| Cubic separator | named sparse exit/compression/delocalization | failed-field classifier absent | local finite support | blocking |
| High separator, unsafe | named sparse exit | failed-field classifier absent | local finite support | blocking |
| High separator, safe | typed Type-B handoff | full decorated-envelope payload absent | local finite support | blocking |

The repair sketch's table is total only for rejecting one proposed interpretation of CT8. It is not total for node `[144]` and cannot support a scope-obstruction verdict.

## Practicality and termination

- Largest legitimate enumerated universe: the supplied pattern edge list and the union of two retained finite supports.
- Parameter controlling it: actual pattern length and support incidence count.
- Ambient-size complexity: a quadratic pair scan plus deterministic BFS/common-prefix work is polynomial.
- Certificate checker complexity: linear in the two supplied support/path certificates, plus the finite failed-field table.
- Cycles and decreasing measures: no loop is needed for the germ comparison; any compression route requires strict `Problem.rank` decrease.
- Hidden global computation: enumerating all outside path contexts would be invalid and is unnecessary for the finite geometric refinement.

## TeX--Lean--framework correspondence

- Exact statement match: **fails in the sketch's obstruction analysis**. The source manuscript does not state routing-label equality as all-context external equivalence.
- Generic ownership audit: germ construction/classification and decorated-envelope payload belong in `Graph`; exact CT execution belongs in its CT namespace; any stable handoff belongs in `Routes`.
- Problem-specific layer is thin: not yet applicable.
- Transfer example exists for new route: no new successful route exists yet.
- `sorry`/`admit`/unregistered `axiom` search: none in the inspected CT3/CT7/CT8 and homogeneous-pattern cone.
- Trust base: no new external theorem is justified; only the registered HSS theorem remains permitted.
- Source manuscript hash during audit: `59ca045186cd45af9b34cacad71fcb91fad2fa7b8b78628d9691f8d7ffb287eb`, unchanged from the sketch baseline.

## Findings

### Blocking

1. **Countermodel/domain mismatch.** The family `X_a,K_d` is not realized inside the exact node-`[144]` branch state. It therefore cannot establish a scope obstruction for that residual.
2. **False necessity claim.** The sketch treats all-context response reflection as necessary for routing-label pigeonhole. The source uses the label only to choose two edges and then analyzes the actual germs; a response mismatch is intended to become an exit, not a contradiction to label legality.
3. **Uniform-alphabet claim not attacked.** Unbounded omitted path length proves coarse collisions, not unbounded cardinality of the listed label alphabet. A coordinate-by-coordinate range audit is missing.
4. **Premature methodology-level obstruction.** The sketch itself identifies a finitely encoded separator/parallel residual with polynomial checking. Under the repair protocol this remains a level-2/3 design problem, not a level-4 proof-language scope obstruction.
5. **Node leaves remain open.** No certified parallel reduction, cubic-switch classifier, or complete high-separator Type-B trigger is constructed.

### Required cleanup

1. Replace “methodology-level obstruction” with the narrower result actually proved: unrestricted path response has infinite context index, so the listed coarse label cannot be used *as an exact all-context external type* without additional structure.
2. Correct the CT8 worksheet: the live Lean CT8 contract has finite response contexts and a caller-supplied total smaller-object operation; it does not itself certify all-context equivalence or target-preserving removal.
3. Remove “CT8 recovery to CT10/CT3” as an existing route. No such compiled route is registered.

### Advisory

- Retain the path-response lemma as a useful warning against conflating coarse routing labels with exact external types.
- Record the fixed-product range audit separately from the post-pigeonhole germ relation; they discharge different obligations.

## FAIL disposition

- Exact obligation returned to the repair loop: prove or refute a graph-independent bound for the **actual listed routing-label coordinates**, then execute the deterministic germ relation without assuming label equality is external equivalence.
- Negated residual if the proposed exact-type lemma is false: equal coarse label with distinct exact germ response, represented by two concrete node-`[144]` states and a typed distinguishing payload—not arbitrary unattached paths.
- Methodology section re-entered: level-2 label/type defect and both-sides invariant selection; level 3 only if a new stable payload is required.
- New invariant attempted: fixed coarse product label followed by `parallel | cubicSeparator | highSeparator` on the two actual canonical germs.
- Proof or reusable contract that discharged the obligation: none yet; the attempted invariant only defeats the claimed scope obstruction.
- Complete audit rerun after repair: yes, on the current sketch; it remains FAIL.

## Verdict

**FAIL.** The sketch rigorously proves an infinite-index theorem for unrestricted path responses, but it neither embeds that family in the exact node-`[144]` residual nor shows that all-context response equivalence is required by the manuscript's coarse-label-plus-geometric-routing argument. A finer finite local invariant remains expressible, so the claimed methodology-level obstruction is not established. Node `[144]` also remains unproved because the parallel and separator consumers are incomplete.

---

## Final independent rerun (iteration 3, superseding scope assessment)

This section audits the complete current repair artifact and implemented cone,
including the ordered-BFS germ classifier, root/after-edge incidence split,
`CubicStarDecomposition`, high-separator port classification, square exits,
and triangular route adapters.  The earlier sections remain as defect history;
where their implementation inventory differs, this section is authoritative.

### Baseline

- Repair sketch: `proofs/erdos_64_eg/repairs/node_144_routing_germ_bottleneck.tex`.
- Current original-manuscript hash:
  `6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`.
  This differs from the first-audit baseline because the source manuscript was
  edited during the larger working-tree expansion.  The current source still
  states the full node-[144] conclusion.
- Failed claim: `lem:same-token-bottleneck-routing`, namely that every
  homogeneous matching/star above one fixed `Q_geom` realizes a named sparse
  exit or a decorated Type-B handoff.
- Methodology re-entered: both-sides finite-invariant test, exact CT trigger and
  payload audit, branch-leaf totality, practical local computation, and
  TeX--Lean--web correspondence.
- Final verdict: **FAIL/blocking**.  Node `[144]` cannot be green.

### Provenance matrix

| Used state | Exact producer | Earlier and independent? | Current disposition |
|---|---|---:|---|
| Activated selected counterexample and exact pair schedule | verified surplus activation cone through node `[136]` | yes | admissible |
| Exact overloaded token--role fibre | `SurplusClasswiseOverload.RoutedOverload`; nodes `[137]`, `[139]`, `[141]` | yes | admissible |
| Literal threshold-sized matching or star in that same fibre | `SurplusHomogeneousPattern.Audit`; nodes `[140]`, `[142]`, `[143]` | yes | admissible |
| Per-pair blocked/free predecessor branch | `SurplusRoutingSupport.classify` | yes | admissible |
| Retained carrier, token root, BFS closure `Zstar`, endpoint germs | `SurplusRoutingGerm` | derived from the exact pair | admissible geometry candidate; not proved equal to manuscript `Z` |
| Prefix/root-divergence/after-edge classification | `OrderedBFSTree`, `RootedPathRelation`, `SurplusRoutingGerm.classifySelectedGerms` | derived from exact germs | admissible and exhaustive for those germs |
| Root/after-edge cubic/high incidence split | `RootIncidence` plus surplus adapters | derived from classifier payload | admissible structural ownership |
| Cubic piece/context decomposition | `CubicStar`, `PackedBoundariedGluing`, `CubicStarDecomposition` | independent generic theorem | admissible decomposition only |
| High-centre ports and OO/OT/TO/TT classification | `HighSeparatorPort`, `SurplusHighSeparatorPort`, `HighSeparatorPortClassification` | independent generic theorem | admissible local port data |
| Sparse-exit or complete decorated Type-B conclusion | manuscript proof paragraph | no Lean producer | **unproved/restates desired output** |

The Lean endpoint confirms the scope precisely:
`GeometricBottleneckOutcome.geometricResidual` contains the exact overload and
`SurplusPatternGermAudit.VerifiedStage`; it contains neither a sparse-exit
certificate nor a Type-B handoff.  `VerifiedGeometricBottleneckClassificationPrefix`
therefore verifies only a prefix, not node `[144]`.

### Quantifier and both-sides attack

| Claim attacked | Literal obligation | Counterexample/failure test | Result |
|---|---|---|---|
| Listed routing labels form one fixed alphabet | every coordinate has a graph-independent finite range before pigeonhole | the listed `P13` attachment entries range over an ambient-dependent inventory | the repair correctly delays `P13`; the fixed coarse product can be bounded by `884736`, but this bound is not an implemented exact node-[144] label theorem |
| Delayed attachment mismatch gives a target cycle or named exit | for every unequal pair of complete selected-window attachment rows, construct the full exit payload | an induced `P13` with pendant leaves attached at different path positions is still a tree | **false without extra geometry** |
| Delayed attachment compatibility closes the branch | one pairwise compatible row must supply a whole-family consumer for its token class | pairwise equality/compatibility does not give simultaneous realization, fan assignment, or response preservation | **unproved quantifier jump** |
| Parallel germs imply quotient/compression/delocalization | for each prefix pair, produce exact same-interface pieces and either a concrete distinguishing context or a certified target-preserving reduction | current classifier stores path geometry only | **missing CT3/C2 payload** |
| Cubic separator has exactly three semantic switch outcomes | structural three-incidence ownership must construct a finite complete context generator or certified quotient result | the cubic claw has all incidence geometry but no cycle, sparse exit, or replacement | **geometry does not imply semantics** |
| High separator is exactly a decorated Type-B envelope | every classified pair must supply all fan assignments, remainder membership, safety decisions, and provenance | open--open endpoint failure and compatible open--open pairs supply none of these automatically | **false as an automatic identification** |
| A triangular side closes the entire branch | local CT5/CT1/CT9 stages must discharge the global node residual | CT1 needs caller-supplied returns/avoidance; CT5/CT9 return further typed residuals | **local stage is not global closure** |

Injection versus surjection, representative existence, pairwise versus
simultaneous realization, and rank versus Boolean/external-response data were
all tested.  No implementation constructs a smaller admissible representative
from routing-label equality, and no pairwise port/attachment classification
realizes the full Type-B family simultaneously.

Both sides of the proposed fixed invariant remain unequal:

- Positive side: the coarse product has a plausible paper bound, and the
  post-selection germ comparison is executable.
- Negative side: the first mismatch is not uniformly converted into a named
  sparse exit, while the all-compatible side is not converted into a complete
  response/Type-B consumer.

Thus the invariant is measurable but not paying on both sides.

### Exact residual leaves and available contracts

| Live leaf | Existing typed contract that applies | What it actually proves | Missing payload / verdict |
|---|---|---|---|
| No repeated fixed coarse label | finite pigeonhole / CT9-style overload | would bound the pattern after an implemented exact code and cardinal theorem | exact node-[144] code producer and delayed-`P13` continuation absent; **open** |
| Delayed `P13` mismatch | none total | no current theorem turns a bare row mismatch into a cycle | token-class-specific A/B certificate absent; **blocking** |
| Delayed `P13` compatible inventory | CT10 is a design shape only | could classify an explicit finite table | whole-family consumer for window, remainder-surplus, and primitive classes absent; **blocking** |
| Parallel / left or right prefix | CT3 is expressible | CT3 can consume exact pieces plus a separating context | same interface, finite complete context generator, target-defect certificate, or certified reduction absent; **blocking** |
| Root cubic | `CubicStarDecomposition` | exact boundary, ownership, reconstruction, baseline, preconnectedness | CT3 response coordinates, target-complete compression, and delocalization decisions absent; **blocking** |
| After-edge cubic | same decomposition | same structural result | no switch classifier or named sparse-exit consumer; **blocking** |
| High: shared shoulders | four-cycle theorem | literal length-four cycle | closes this subleaf as C1; **closed subset only** |
| High: endpoint-in-opposite-shoulders with at least one triangular port | triangular square theorems | literal length-four cycle | closes this subleaf as C1; **closed subset only** |
| High: endpoint failure, open--open | no current square theorem | classifier records first failure | neither triangle nor other target/exit payload; **blocking** |
| High: compatible triangular port | triangular shoulder CT5 adapter; conditional CT1 return adapter | executes a local verified stage under its explicit prerequisites | return/avoidance, remaining port, fan assignment, and global handoff remain; **blocking globally** |
| High: triangular--triangular | CT9 cross-shoulder adapter | executes the exact TT local stage | its downstream residual is not a node-[144] disjunction; **blocking globally** |
| High: compatible open--open | `FanClosedPort` only after additional input | can consume a completed assigned fan profile | recovered ports are not identified with canonical surplus slots; remainder membership, four shoulder assignments, admissibility, safety, compression/delocalization, and marked provenance absent; **blocking** |
| High: third/predecessor port | port classifier and triangular adapters | classifies the extra incidence | no leaf-total composition with the divergent pair; **blocking** |

No currently registered route closes all rows.  Specifically:

- CT8 remains inapplicable: there is no finite exact response type with a
  semantically valid total `remove` operation.
- CT9-to-CT7 expects a capacity-one overload pair, not this classwise overload
  followed by greedy pattern extraction.
- CT17 expects bounded thickening/compatibility data not supplied by a long
  germ.
- `OpenPortCompatibility` and `FanClosedPort` require canonical slot and fan
  payloads not established by recovered high-separator ports.
- The new triangular route adapters preserve prerequisites rather than
  manufacturing them, correctly preventing branch leakage.

### Branch, invariant, and reused-handoff audit

- Positive-side payment/account: only the pre-existing quadratic-spine branch
  is closed, by `geometricBottleneck_quadraticSpine` from the exact negative
  overload decision.
- Negative-side bounded witness/consumer: germ geometry is bounded and
  executable, but semantic consumers are incomplete as tabulated above.
- Measurability: PASS for retained carrier, BFS, prefix comparison, incidence
  scan, cubic decomposition, and high-port predicate tables.
- Ladder legality: the remaining work is a level-2/3 finite residual design,
  not a justified methodology obstruction.
- Cross-branch leakage: the manuscript's high-separator paragraph imports
  decorated fan admissibility and context-universality conclusions that the
  exact residual does not contain.  The Lean implementation correctly avoids
  this leakage by returning `geometricResidual`.
- Theorem weakened or assumption added: Lean has not proved the manuscript
  theorem; it has honestly implemented a weaker prefix.  Calling that prefix
  node `[144]` would weaken the node contract.
- Reused handoffs: the square exits are independent and exact; cubic
  decomposition and triangular adapters are reusable but do not close their
  parent branch.  There is no cyclic route, so no decreasing-measure issue is
  hidden.

### Practicality and termination

- Largest legitimate local universe: one literal homogeneous pattern, its
  retained support lists, two ordered-BFS trees/germs, and constant-size
  incidence/port tables.
- Controlling parameters: selected-graph order `n`, support incidence count,
  and pattern size.
- Implemented ambient complexity: polynomial; `zstarBudget_polynomial` and
  the linear/constant predicate budgets verify this at their stated scopes.
- Proposed delayed scan: static `O(13 n^2)` envelope in the repair sketch;
  no exact node-[144] implementation/checker yet.
- Fixed coarse label: claimed paper cardinality `884736`; no compiled producer
  currently connects it to the exact overload.
- Cycles/termination: classifiers are finite scans with no recursive route
  cycle.  Any eventual replacement branch must expose strict problem-rank
  decrease.
- Hidden global computation: none in the implemented geometry.  The manuscript
  appeal to all compatible outside contexts is not an implemented practical
  checker and cannot be used as if enumerated.

### TeX--Lean--web--trust correspondence

- TeX statement: full sparse-exit-or-decorated-Type-B disjunction, followed by
  fixed homogeneous caps and the near-cubic spine.
- Lean statement: exact overload-vs-quadratic decision plus an unconsumed
  geometric residual.  **Statement match fails for node `[144]`.**
- Web status: `erdos.same-token-bottleneck` remains `.next`, and its notes say
  node `[144]` is the frontier.  This is honest and must not be changed to
  implemented/green.
- Ownership: reusable BFS, gluing, cubic, incidence, and high-port logic is in
  Core/Graph/Routes; the Erdős file is thin.  PASS at the implemented scope.
- Transfers: non-Erdős transfers exist for the new generic structural units
  and local high-port routes.  They validate reuse, not the missing Erdős
  semantic composition.
- Focused builds: PASS for
  `SurplusPatternGermAudit`, `CubicStarDecomposition`,
  `HighSeparatorPortClassification`,
  `HighSeparatorPortClassificationRoutes`, and
  `CT10GeometricBottleneckClassification`.
- Full web/export build: FAILS in the current dirty working tree at
  `Erdos64EG/P13PartIVFiniteRouting.lean` (missing `Decidable`, `Prop` used
  where `Type` is required, and heartbeat timeout).  These errors are outside
  the focused node-[144] cone, but they prevent a successful global
  synchronization check in this audit.
- `sorry`/`admit`/axiom search: no `sorry` or `admit` in the inspected cone.
  The only project-specific axiom found is
  `External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle`.
- `#print axioms`: node-[144] classifier declarations use only standard Lean
  axioms (`propext`, `Classical.choice`, `Quot.sound`); the existence endpoint
  additionally uses the sole allowed HSS theorem.  Trust scope PASS.

### Findings

#### Blocking

1. No implemented fixed coarse-code selection plus delayed-`P13` A/B/C
   classifier consumes the exact node-[140]/[142]/[143] pattern.
2. Parallel and cubic branches have structural decompositions but no CT3/C2
   semantic payloads or leaf-total sparse-exit classifier.
3. High branches close only square subcases.  Open--open endpoint failures and
   compatible open--open pairs remain live; triangular stages do not discharge
   the global residual.
4. No theorem identifies the generic `Zstar` candidate with the manuscript
   `Z(pi;t,r)` while transporting all token, role, marked/unmarked, blocker,
   and exit provenance.
5. There is no total route from `GeometricBottleneckOutcome.geometricResidual`
   to `sparse exit ∨ decorated Type-B handoff`; consequently the cap theorem
   and near-cubic consequence cannot be derived.
6. The current global WebExport build is not clean, independently preventing
   a green/synchronized release state.

#### Required cleanup

1. Keep node `[144]` white/next and describe the Lean endpoint as a geometric
   classification prefix, not a formalization of the manuscript bottleneck.
2. Do not cite `CubicStarDecomposition`, port classification, or triangular
   adapters as branch consumers; document their narrower producer/adapter
   scope.
3. Re-run the full example/WebExport build after the unrelated Part-IV errors
   are repaired.

#### Advisory

- The next coherent implementation unit remains the delayed `P13` A/B/C
  classifier, split by window, remainder-surplus, and primitive token class.
- After that classifier, implement CT3 semantics for prefix/cubic leaves and a
  complete open--open/Type-B handoff producer.  Re-run this entire checklist;
  local PASS results should be reused, not re-proved.

### FAIL disposition

- Exact obligation returned to the repair loop: construct a total executable
  function on the exact repeated-coarse-code pair that returns (A) complete
  direct-target data, (B) a complete named sparse-exit certificate, or (C) a
  whole-family payload whose typed geometric branch is consumed to a complete
  decorated Type-B handoff.
- Negated residuals: delayed attachment mismatch without target data;
  prefix/cubic geometry without response semantics; open--open endpoint
  failure; compatible open--open without fan assignment/provenance; and local
  triangular stages with unconsumed downstream residuals.
- New invariant attempted: fixed coarse product, delayed `P13` scan, exact
  ordered-BFS geometry, cubic decomposition, and typed high-port pair table.
  It improves measurability and ownership but fails the negative-side consumer
  test.
- Existing contract that discharges the whole obligation: **none**.  Existing
  contracts close only the square subleaves and supply reusable structural or
  conditional stages.
- Complete audit rerun after current repair: **yes**.

### Final verdict

**FAIL/blocking.  Node `[144]` cannot be green.**  The current implementation
is a sound, practical, well-owned geometric-prefix expansion, and several
subcomponents independently pass.  It does not prove the manuscript's
sparse-exit-or-decorated-Type-B disjunction, and no existing typed contract
closes all residual leaves.

---

## Iteration 4 red-team rerun: typed semantic residual split

### Baseline

- Repair sketch: `proofs/erdos_64_eg/repairs/node_144_routing_germ_bottleneck.tex`.
- Original manuscript hash before and after this iteration:
  `6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`.
- Edited scope: the separate repair sketch and this audit only. The original
  manuscript and the concurrently rewritten
  `Graph/SurplusPatternCoarseRouting.lean` were not edited.
- Verdict: **FAIL/blocking**.

### Exact residual and trigger matrix

| Residual | Exact local payload | Intended consumer | Missing S-Trig field | Verdict |
|---|---|---|---|---|
| Delayed attachment mismatch | Same selected graph/fibre/pattern/collision, one window-position--vertex coordinate, both rooted supports, unequal literal bits | C1 target cycle or one named sparse exit | Connector, cycle edge list, simplicity/length certificate, or complete exit witness | Blocking |
| Parallel/prefix germs | Two actual germs, prefix proof, equal coarse code, equal attachment rows | CT3 target defect or certified compression | Common boundary/pieces and concrete distinguishing context or smaller target-complete representative | Blocking |
| Cubic separator | Exact cubic incidence, cubic star, owned `Fin 3` boundary, reconstruction and provenance | CT3 defect/compression/delocalization | Target-response coordinates and reflection/reduction certificate | Blocking |
| Compatible open--open high separator | Exact high centre, distinct open ports, endpoint/shoulder table and source provenance | Existing Type-B ledger entry | Remainder support, assigned carriers, marking, fan assignment, safety/admissibility and ledger provenance | Blocking |
| Open--open endpoint failure | Exact first failed endpoint field | C1 or named sparse exit | The triangular square theorem does not apply; no alternative target/exit payload | Blocking |

### Quantifier and contract attack

- An attachment-bit inequality is not a cycle witness. The two-pendant-leaf
  induced-path tree remains a finite countermodel to that local implication.
- A prefix relation is not equality of external response, and supplies neither
  `exists context` nor `for all compatible contexts`.
- Exact cubic incidence ownership is not a CT3 semantic result.
- Two pairwise compatible open ports do not provide one simultaneous assigned
  Type-B fan entry.
- CT10 can classify these rows but cannot construct their consumer proofs.
- The registered CT9-to-CT7 route has the wrong source residual.
- A new `Consumer` structure containing functions from these residuals to the
  desired conclusions would be proof injection and was rejected.

### Both-sides, practicality, and scope classification

The residual split is locally measurable. Collision selection is quadratic in
the literal pattern length; retained-support BFS/common-prefix work is linear
in the two supports; cubic/high incidence tables are local-neighbour scans with
constant-size port classification. No contexts, quotients, paths, subgraphs,
graphs, or graph families are enumerated.

The split still fails the both-sides test because none of the five live leaves
has C1--C5 or an admitted typed consumer trigger. This is **not** a proved
methodology-level scope obstruction: every missing witness is expressible in
the current language as a finite proof-carrying context, replacement, CT3
certificate, or assigned Type-B support. The failure is a level-3 pattern and
producer theorem gap. The first exact failing obligation is delayed-mismatch
S-Trig.

No generic route or transfer example was added because no sound
residual-to-trigger transformation was obtained. Adding a transfer for a
caller-supplied semantic certificate would validate only proof injection.

### Iteration 4 verdict

**FAIL/blocking.** The finer typed split improves the residual registry and
rules out a false scope-obstruction claim, but does not close node `[144]`.
The original manuscript remains unchanged and node `[144]` must remain white.
