# Repair audit: nodes 22--24 window-density realization

## Defect freeze

- Defect ID: EG-P13-WINDOW-REALIZATION-22-24.
- Stable nodes: 22--24, expanded by 145--157.
- Failed implication:

  For the 91 barrier indices i, node 21 proves finite safe and flat counts
  W_i and F_i and the product inequality

  2^118 * product F_i < product W_i.

  The manuscript then inferred a finite graph-completion state family S and a
  response map rho : S -> (I -> Bool) satisfying

  for every assignment epsilon : I -> Bool, there exists s in S with
  rho s = epsilon.

  The count statements do not imply this simultaneous realization. They also
  do not imply that independently chosen states at distinct packed windows
  commute under graph gluing.
- Classification: design defect D, level-2 local branch repair with a possible
  level-3 reusable finite-filtration contract.
- Smallest verified ancestor: VerifiedP13MultiScaleCurvaturePrefix on the
  bounded-surplus constructor of the exact node-19 route.
- Immutable blast radius: node 24 cannot construct its numerical
  P13CoverageResidual; consequently node 25 cannot consume a proved density
  ceiling. No earlier green node is affected.
- The source manuscript is frozen during this repair iteration. The current
  source already records the defect as an open interface; no new mathematical
  claim will be merged until red-team PASS.

## Directed branch state

The active branch is

B = (H0, order, exits, invariants, residual, vocabulary, queue, artifacts).

- H0: the selected packed finite graph is a lexicographically minimal
  minimum-degree-three counterexample and avoids every power-of-two cycle.
- order: lexicographic packed graph rank, inherited unchanged.
- incoming path: official target avoidance; CT1/CT2/CT3 minimal prefix;
  induced-P13 CT1; CT12 maximum P13 packing; CT10 legal-label algebra;
  exact node-19 squared-scale split; bounded-surplus constructor; node-21
  multi-scale curvature certificate.
- certified absent exits on this constructor: the strict non-near-cubic scale
  constructor is not active. Target cycles and proper certified reductions are
  excluded by the inherited minimal-counterexample context.
- inherited invariants:
  - exact selected CT12 packing and P13-free remainder;
  - legal attachment labels and symbolic C_s semantics;
  - 91 accepted barrier indices;
  - audited W_i and F_i counts;
  - strict integer product rate floor;
  - bounded total-surplus squared inequality.
- residual: bounded-surplus, target-avoiding selected graph after node 21,
  before any window-density conclusion.
- finite vocabulary: selected windows, Fin 13 path positions, 399 legal
  labels, 91 barrier indices, fixed compatibility rows, actual attachment
  states, finite ordered barrier schedules, and explicit omitted assignments
  or first failing fibres.
- queued payloads:
  - hot full-filtration ledger -> CT15/CT4 capacity comparison;
  - first failing conditional fibre -> CT6 first failure, then CT7/CT10;
  - cold ambient-cubic window incidences -> node 153 corridor producer;
  - target distinction -> existing literal target-defect consumer;
  - neutral smaller exchange -> CT3 compression.
- artifacts: node-21 Lean certificate/audit shards, local Boolean classifier,
  graph-owned cold arithmetic, cold G1/G2/G3 terminal routes.
- unavailable facts:
  - a dyadic completion-state enumeration;
  - arbitrary simultaneous realization;
  - cross-window commuting gluing;
  - a concrete cold corridor/germ producer and overlap constant;
  - finite context-code reflection for every compatible outside context.

## Quantifier normalization

- Claimed domain: the 91 barrier coordinates, repeated over a declared
  dyadic-scale schedule and over all selected windows.
- Claimed codomain: Boolean response assignments.
- Injection actually available: node 21 proves only injective indexing of the
  finite barrier table and semantic equality of fixed compatibility rows.
- Realization required by the discarded argument: surjectivity of one response
  map onto the full Boolean cube.
- Exact negation: there exists a Boolean assignment omitted by every admissible
  completion state.
- Canonical witness: the first omitted assignment in the explicit coordinate
  order, or, for the refined filtration below, the first prefix fibre whose
  safe-to-flat ratio fails.
- Determinism: FinEnum order for assignments and OrderedCollection order for
  barrier stages.

Two-coordinate countermodel: state responses {00, 11}. Each coordinate sees
both Boolean values, but assignments 01 and 10 are omitted. Thus coordinatewise
nonconstancy and injectivity do not imply simultaneous realization.

## Resource inventory

| Resource | Producer | What it can pay | Remaining capacity |
|---|---|---|---|
| 91 barrier rows and counts | node 21 CT10 | exact finite W_i/F_i arithmetic | all rows unused |
| strict product rate floor | node 21 | rounding-free aggregate comparison | one aggregate charge |
| actual selected windows | CT12 packing | local supports and disjointness | every selected window |
| actual attachment labels | graph attachment layer | 13-bit adjacency response | every outside vertex |
| target avoidance | minimal context | eliminates literal G1 cycles | persistent |
| minimality and CT3 | nodes 1--14 | neutral smaller replacement contradiction | persistent |
| bounded surplus | node 19 bounded constructor | pays non-cubic-window loss | one exact ledger |
| 15/13 cold arithmetic | nodes 151--152 kernel | branch-excess incidence supply | each ambient-cubic window |

## Both-sides candidates

| Predicate | Positive payment | Negative residual | Measurable from | Consumer | Admit? |
|---|---|---|---|---|---|
| Complete Boolean realization | Boolean entropy bound | first omitted assignment | explicit states and responses | CT10/CT7 | rejected as primary invariant: state producer absent |
| Every sequential barrier fibre pays W_i/F_i | product cardinality charge | first ratio-failing prefix fibre | explicit finite filtration | CT6 then CT7/CT10 | selected |
| A cold incidence reaches an earlier exit | target or typed handoff | first quiet stage | canonical corridor scan | CT1/CT7 | selected downstream |
| Same-interface context table distinguishes | target defect | response-neutral exchange | finite context code plus reflection | CT3 | selected downstream |

Selected invariant: the earliest barrier stage at which the conditional
safe-to-flat ratio fails. This lies before Boolean-cube realization on the
invariant ladder and turns failure into an explicit finite fibre.

## Proposed CT route

### Sequential filtration

- S-Def: a finite state type, ordered barrier stages, a nested prefix-state
  family A_0 superset A_1 ... and exact per-stage safe and flat numerators.
- S-Dich: at the first stage, either
  W_i * |A_{i+1}| <= F_i * |A_i|,
  or the strict reverse inequality is returned with the exact prefix fibre.
- S-Equiv: membership in A_{i+1} is the graph response condition for barrier i.
- S-Pers: all states in a prefix retain the same selected graph, window,
  boundary data, and earlier response decisions.
- S-Det: first failure uses the declared barrier order.
- S-Rout: all-paying branch emits a multiplicative ledger; failure emits the
  exact stage and prefix fibre.
- S-Trig: all-paying enters CT15/CT4 only after target-relative independence is
  certified; failure enters CT7/CT10 with the stage response datum.
- S-Comp: multiplying the cross-multiplied inequalities telescopes without
  division or logarithms.
- S-Meas: remaining schedule length.
- Work: one finite cardinality scan per declared stage; no graph universe.

### Cold corridor

- S-Def: actual external incidence token, canonical finite connector word, and
  ordered stage positions.
- S-Dich: first target/handoff/merge/degree failure, or quiet bounded germ.
- S-Pers: selected window and inherited target avoidance are unchanged.
- S-Rout: G1 -> CT1, G2 -> literal target defect, G3 -> CT3.
- S-Meas: remaining connector-word length.

## Autonomous lemma ledger

| Required statement | Available inputs | First attempt | False implication | Refined residual | Next route | Status |
|---|---|---|---|---|---|---|
| Complete 91-bit realization | node-21 counts | reuse BooleanStateEntropy | separate counts imply surjection | first omitted assignment | CT10 | rejected |
| Cross-window product | CT12 disjoint supports | multiply local states | vertex-disjoint supports imply commuting gluing | first interfering pair | CT7 | open |
| Multiplicative entropy without realization | ordered finite filtration | cross-multiply each ratio | none at generic finite level | first ratio-failing fibre | CT6/CT10 | generic runner and P13 weight adapter verified; actual connector states constructed, global completion semantics open |
| Actual 91-barrier connector presence | selected graph/window and bounded sequences | enumerate `n^15` literal connector words | coordinatewise paths are not mutable global completions | first missing connector or all-present ledger | graph reflection / separator route | graph-owned classifier verified; neither side yet closes |
| Concrete node-153 germ | literal cold cubic external stub and CT2 bridgelessness | canonical deleted-edge return plus generic first-failure scan | constant-bounded target-relative germ does not follow from ambient finiteness | honest ambient-finite structural germ or explicit scale-long residual | finite target-relative classifier / CT17 | graph-owned corridor producer verified; constant bound open |
| CT17 long-scale entry | explicit long corridor | instantiate CT17 from length alone | length supplies positions but no target/offset/value/compatibility reflection or finite scale limit | exact branch-indexed long-support handoff | graph semantic thickening producer | pre-CT17 handoff verified; CT17 trigger open |
| First ratio-failing fibre | exact arithmetic failure | relabel as CT6/CT7/CT10 residual | no failure data, representative pair, context family, datum classes, or promotion follows | exact branch/profile-indexed arithmetic handoff | graph response-reflection theorem | arithmetic handoff verified; semantic CT trigger open |
| G2 continuation | literal TargetDefective | informal exit-(4) name | target defect resembles exit-(4) | exact context-preserving target-defect payload | verified generic typed handoff; exit-(4) enrichment remains a separate residual | typed handoff verified |

No missing lemma is carried as a hypothesis. Generic profiles may accept raw
finite primitives, but an Erdős node is green only after those primitives are
constructed from the selected graph.

## Leaf-totality target

| Branch | Exact residual | Local object | Route | Progress | Leaf |
|---|---|---|---|---|---|
| all filtration ratios pay | multiplicative ledger | finite state filtration | CT15/CT4 | product inequality | C4 or typed ledger |
| first ratio failure | stage plus prefix fibre | conditional response family | CT6 -> CT7/CT10 | earlier stage index | target defect, refinement, or cold incidence |
| cold G1 | actual dyadic cycle | cycle witness | CT1 | immediate | C1 |
| cold G2 | literal context distinction | two pieces plus exact outside context | verified target-defect handoff | exact context and provenance preserved | typed residual; not yet C1--C5 closure |
| cold G3 | target-complete smaller replacement | literal compression | CT3 | smaller rank | C2/C3 |

## Practicality

- Local alphabet sizes: 91 barriers, 399 labels, 13 path positions.
- Runtime target: polynomial in the explicit state table and barrier schedule.
- Certificates: fixed node-21 bit rows and local cardinality/reflection proofs.
- Termination: first failure decreases remaining schedule length.
- No SimpleGraph universe, subgraph universe, or global context universe is
  enumerated.

## Merge gate

The source proof may be changed from open interface to theorem only after:

1. the generic sequential-filtration theorem and transfer fixture compile;
2. its P13 states and response semantics are graph-owned;
3. every first-failure residual has a typed consumer;
4. concrete cold corridor/germ coverage and G2 continuation compile;
5. the red-team repair skill returns PASS;
6. Lean, manuscript, web, and repository checks pass.

## Red-team iteration 1

Verdict: **FAIL**.  The complete checklist is recorded in
`nodes_22_24_window_density_realization.redteam.md`.

The sequential arithmetic contract is sound, but its complete branch can be
vacuous when the terminal fibre is empty, and a ratio-failing fibre has no
graph-semantic CT6/CT7/CT10 payload by arithmetic alone.  The concrete cold
return is graph-owned, but its quiet support is bounded only by the ambient
vertex count.  Exact dyadic target response distinguishes arbitrarily long
two-boundary paths, so no constant response code may erase length/scale.  The
repair loop therefore retains terminal nonemptiness, semantic reflection,
long-scale routing, and the bare target-defect consumer as explicit residual
obligations.  No node-[24] ceiling is admitted in this iteration.
