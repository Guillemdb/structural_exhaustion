# Red-team audit: nodes [21]--[24] weighted hot/cold handoff

## Baseline and scope

- Repair sketch:
  `proofs/erdos_64_eg/repairs/nodes_21_24_weighted_hot_cold_handoff.md`
  (SHA-256
  `895d7faff4c41ab972f36ec491e7bf1ad45057d5cdc5a0846a06cb374a95fde2`).
- Original manuscript baseline:
  `original_erdos_64_proof.tex` (SHA-256
  `215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`).
- Current synchronized manuscript inspected:
  `proofs/erdos_64_eg/erdos_64_proof.tex` (SHA-256
  `02ad7f6e6dc3aa466f1b8977342b33d39d0624138746f2fb9869405da6135da9`).
- Failed implication: node [21]'s 91 safe/flat count rows were promoted to a
  simultaneously realized independent Boolean package and then multiplied
  across scales and windows.
- Methodology consulted: branch-state provenance, residual normalization,
  both-sides selection, CT6 first failure, CT7 exchange, CT10 refinement,
  CT15 rank forcing, typed handoffs, level-2 repair, and level-3 interface
  review in `framework/branch_closure_methodology_extended.tex`, together
  with the red-team checklist.
- Source manuscript and Lean files were not edited during this audit.

The verdict is intentionally split:

1. **Statement/handoff repair: FAIL, but the proposed invariant is the right
   repair direction.**  The exact sequential weighted filtration is a sound
   replacement for the false Boolean-cube inference.  The sketch does not yet
   define the graph-owned producer or prove either typed connection from its
   outputs to the manuscript consumers.
2. **Full nodes [22]--[24] density closure: FAIL.**  No current Lean theorem
   derives the window-density cap, entropy overflow contradiction, or
   high-entropy cap from the weighted filtration.

## Directed-flow reconstruction

The relevant original flow is

```text
[17] selected maximal induced-P13 packing
  -> [18] P13 label algebra
  -> [19]/[20] sparse-surplus split and near-cubic spine
  -> [21] finite curvature enumeration and c13 table
  -> [22] packing-density decision
       -> [23] entropy overflow
       -> [24] density cap
  -> [25] remainder.
```

Part XI expands the intended negative entropy branch:

```text
[145] hot/cold interface
  -> [148] live-hot comparison
       -> [149] density cap
       -> [150] linear cold mass
  -> [151] ambient-cubic cold windows
  -> [152] thirteen branch-excess stubs per such window
  -> [153] bounded first-failure extraction
  -> [154]--[157] hit / defect / handoff / compression.
```

The smallest independently verified predecessor is
`VerifiedP13MultiScaleCurvaturePrefix`.  It supplies the selected packing,
the 91 ordered indices, exact safe/flat counts, and the integer product bound

```text
2^118 * p13BarrierFlatProduct < p13BarrierSafeProduct.
```

It does **not** supply a finite completion carrier, 91 graph predicates,
separated-scale copies, a state-to-labelled-skeleton injection, or
cross-window gluing.

## Provenance matrix

| Used fact | Earlier producer | Earlier on path? | Independent of failed implication? | Verdict |
|---|---|---:|---:|---|
| Exact selected packing | CT12 / node [17] | yes | yes | available |
| 91 barrier indices and order | node [21] | yes | yes | available |
| Exact `W_i`, `F_i` counts | node [21] | yes | yes | available |
| Integer product floor `2^118 F < W` | node [21] | yes | yes | available |
| Exact decimal rate `118.108581006...` | manuscript computation | yes | yes | not exported by the filtration theorem |
| Finite graph-owned weighted state carrier | none | no | n/a | **missing** |
| Executable flat predicate reflected to each node-[21] relation | none | no | n/a | **missing** |
| Nonempty initial carrier | none | no | n/a | **missing** |
| Interpretation/injection into distinct labelled skeleton states | none | no | n/a | **missing** |
| Separated dyadic scale schedule | none in this route | no | n/a | **missing** |
| Cross-scale and cross-window product/gluing | none in this route | no | n/a | **missing** |
| First arithmetic failure implies a cold-corridor input | none | no | n/a | **missing** |

## Quantifier attack

| Claim | Literal quantified form | Countermodel or attack | Result |
|---|---|---|---|
| Sequential runner is exhaustive | For every explicit list of states and ordered barrier list, the runner returns a first failed inequality or a complete ledger | inspected the recursive constructors | passes |
| Complete ledger pays the product | For a fixed explicit state list and fixed predicates, `prod safe * final <= prod flat * initial` | checked against `CompleteLedger.product_le` | passes |
| Complete and terminal nonempty gives 118-bit loss | For a supplied profile with nonempty final fibre, `2^118 * final.length < initial.card` | checked against `p13Sequential_complete_state_loss` | passes |
| Three-way result is already formalized | Every run returns underpayment, empty terminal, or hot | current `Outcome` has only `firstFailure` and `complete`; no application theorem splits terminal emptiness | false as a claim of current formal coverage |
| Empty terminal is meaningful progress | A complete run with empty final fibre identifies a missing completion | take `S_0=[]`; every inequality pays and the terminal is empty | requires an independently proved `S_0.Nonempty` or a separate missing-initial-carrier residual |
| Underpayment is a cold-corridor trigger | The first ratio failure constructs the exact cold-window/corridor consumer payload | `SequentialRatioFailureHandoff` explicitly states that it is not CT6, CT7, or CT10 and lacks graph reflection | unproved |
| One complete local run supplies manuscript entropy | A single profile's cardinality loss yields `(c13-o(1)) log n` target-complete states at every scale | no scale family, state interpretation, or injectivity is present | unproved |
| Per-window payments multiply | Complete local ledgers for distinct windows yield a product of global target-complete states | pairwise/local products need not commute; no global gluing theorem is present | unproved |
| 91 Boolean responses encode the rate | A response in `Bool^91` carries `118.108...` bits | `Bool^91` has at most 91 bits; multiplicities are erased | false and correctly rejected by the sketch |

The sketch passes the injection-versus-surjection and rank-versus-cube tests:
it does not infer a Boolean cube.  It fails at the next quantifier boundary:
a cardinality inequality over a supplied finite carrier is not yet a theorem
about graph completions, labelled skeleton states, scales, or products of
windows.

## Branch and invariant audit

- **Positive payment.**  The exact product inequality is valid for one
  supplied explicit profile, and the integer 118-bit consequence is valid
  when its terminal fibre is nonempty.
- **Negative bounded witness.**  `FirstFailure` canonically retains the first
  failed barrier and exact before/after lists.  This is a good finite residual.
- **Empty-terminal witness.**  A complete ledger plus terminal equality zero
  is finite, but the sketch must distinguish an initially empty carrier from
  a first genuine emptying step.
- **Measurability.**  The generic runner is deterministic once the state list
  and barrier predicates have been constructed.  Those application objects
  are not measurable from the current node-[21] state because they have not
  been constructed.
- **Both-sides progress.**  Arithmetic progress is proved on both runner
  outputs.  Manuscript progress is not: neither output satisfies its claimed
  downstream graph trigger.
- **Cross-branch leakage.**  Calling an arithmetic failure a manuscript
  "cold window" imports semantics from `P13HotColdInterface`, whose cold type
  is instead a missing assignment in an application-supplied Boolean system.
- **Theorem weakening.**  The sketch does not weaken the theorem or add
  Boolean realization as an assumption.  Its proposed graph-owned carrier is
  correctly listed as a construction obligation rather than treated as
  proved.

## CT and route obligations

| Route or CT | Exact available trigger | Missing schema or payload | Verdict |
|---|---|---|---|
| Generic sequential filtration | Explicit `FinEnum State`, barrier predicates, weights | none for arithmetic execution | pass |
| Sequential-ratio handoff | `FirstFailure` and run equation | none for arithmetic residual | pass |
| Failure -> CT6 | exact before/after cardinality inequality | graph-semantic activity/failure reflection | **blocking** |
| Failure -> CT7 | no same-interface representative pair or separating context | S-Def, S-Equiv, S-Rout, S-Trig | **blocking** |
| Failure -> CT10 | no finite missing graph label or promotion rule | label alphabet, class table, consumer trigger | **blocking** |
| Complete -> entropy/state count | exact local product inequality | graph interpretation, injectivity, scale ledger, cross-window gluing | **blocking** |
| Cold -> Part XI | current Boolean cold entry or actual 13-bit cold fork | no adapter from weighted failure/empty-terminal certificate to `ClassifiedColdCubicStub` | **blocking** |

No existing route may be cited merely because its destination is already
named in the paper.  The current generic route deliberately stops before any
CT trigger, which is the correct formal status.

## Current Lean correspondence

### What is implemented

- `Core.FiniteSequentialFiltration` implements the exact runner, canonical
  first failure, complete ledger, sublist facts, and telescoping product.
- `Routes.SequentialRatioFailureHandoff` preserves the branch context,
  profile, exact run equation, failure index, fibres, and strict inequality.
- `P13SequentialEntropyFiltration` instantiates the 91 audited node-[21]
  weights and proves the conditional integer 118-bit state loss.
- `P13SequentialRatioFailureAudit` proves that the existing graph-owned
  attachment interface has 13 coordinates whereas node [21] has 91 barriers,
  and explicitly records the missing reflection theorem.
- `P13PartIWindowDensityTriage` decides the density-cap proposition only as an
  arithmetic proposition.  On failure it stores the negated cap; it does not
  prove node [23]'s contradiction.  Its node-[24] structure stores the
  high-entropy conclusion as an open requirement.

### What does not match the sketch yet

- `P13HotColdInterface` classifies an application-supplied Boolean system.
  It is not the weighted multiplicity-retaining filtration proposed here.
- `P13Node160RealizationPackage` still asks for simultaneous realization of
  all 91-coordinate Boolean assignments and global gluing.  Its dichotomy is
  classical existence versus nonexistence of a package, not the executable
  weighted three-way classifier.
- `P13Node21PartXIRoute` uses a separate actual 13-bit attachment fork and
  explicitly proves no density or 91-barrier result.
- No Lean declaration constructs the weighted profile from an actual selected
  window and scale, aggregates it over the packing, proves the exact
  `118.108581006...` comparison, or consumes either negative outcome in the
  cold corridor.

Thus the generic framework ownership is good, and the Erdős layer remains
thin, but the target-specific producer and both typed routes are absent.

## Reused cold-branch audit

| Claimed handoff | Exact trigger proved? | State transported? | Consumer dependency independent? | Verdict |
|---|---:|---:|---:|---|
| Ratio underpayment -> same-window cold branch | no | arithmetic context/window identity can be retained, but no current type does so | cold corridor is independently developed, but its entry type differs | **blocking** |
| Empty terminal -> same-window cold branch | no | no first-emptying payload exists | same issue | **blocking** |
| Cold stub -> F1--F5 -> compression | not completely | partial graph-owned corridor data exist | later D5/D6, compatible-response, equal-state exchange, and complete F1--F5 semantics remain open | **blocking for full closure** |

In addition, the original/current cold prose cannot be treated as an admitted
closed consumer.  Its terminal F5 case does not yet construct the second
same-interface representative in every terminal subcase; the neutral
equal-length row does not yet prove existence of a strictly smaller
representative; and the F2 target-defect classification is not yet connected
to the exact existing ledger trigger.

## Leaf totality

| Leaf | Current exact certificate | Declared consumer | Verdict |
|---|---|---|---|
| First ratio underpayment | `FirstFailure` plus exact strict inequality | arithmetic residual only | pass locally; open globally |
| Complete, terminal empty | complete ledger; no dedicated routed structure | proposed cold branch | **blocking** |
| Complete, terminal nonempty | product inequality and integer 118-bit loss | proposed node [22] entropy input | **blocking** |
| Cross-scale incompatibility | no payload | proposed cold branch | **missing leaf** |
| Cross-window gluing failure | no payload | proposed cold branch | **missing leaf** |
| Density overflow [23] | exact failed finite cap and an open `False` requirement | entropy contradiction | **open** |
| Density handoff [24] | finite cap only on the selected arithmetic branch; high-entropy requirement remains open | remainder and later branches | **open as full manuscript node** |

## Practicality and termination

- The generic runner performs one filtering pass per barrier, hence
  `O(91 * |S_0|)` predicate evaluations.
- The barrier recursion terminates because the remaining barrier list strictly
  decreases.
- No Boolean cube, graph universe, context universe, powerset, or path universe
  is enumerated by the current generic implementation.
- Practicality of the Erdős application is still unproved: no bound is given
  for constructing or storing the proposed graph-owned carrier `S_0` at one
  window and scale.  A finite carrier is not automatically a practical local
  carrier.
- No termination or bounded-overlap audit exists yet for aggregating failed
  scales/windows into the complete cold-corridor route.

## Trust and source audit

The scoped current Lean files contain no `sorry`, `admit`, `axiom`, or
`unsafe` declarations.  The generic runner is constructive.  Classical choice
appears in the separate node-[160] existence dichotomy, not in the executable
sequential runner.  No new external mathematical theorem is introduced by the
repair sketch.

Focused checks completed during this audit:

- `lake env lean StructuralExhaustion/Core/FiniteSequentialFiltration.lean`
  in the framework package: pass;
- `lake env lean Erdos64EG/P13SequentialEntropyFiltration.lean` in the Erdős
  package: pass;
- `lake build Erdos64EG.P13SequentialRatioFailureAudit
  Erdos64EG.P13PartIWindowDensityTriage Erdos64EG.P13HotColdInterface`: pass,
  with only pre-existing unused-variable warnings in replayed modules.

## Findings

### Blocking

1. **Application producer absent.**  Node [21] does not construct `S_0` or
   the 91 exact graph-owned predicates.  The sketch's central classifier
   therefore cannot yet be run on an Erdős branch state.
2. **Initial nonemptiness absent.**  `S_0=[]` makes the complete-empty branch
   automatic and supplies no structural information.  The producer must prove
   initial nonemptiness or route initial emptiness separately.
3. **Positive semantic bridge absent.**  The local 118-bit cardinality loss
   is not a state-count theorem for labelled target-complete graphs and does
   not supply scales or cross-window independence.
4. **Negative semantic bridge absent.**  Arithmetic underpayment and terminal
   emptiness do not construct the Boolean cold type, actual 13-bit fork,
   cold-cubic stub, CT6, CT7, or CT10 trigger currently consumed downstream.
5. **Scale/window leaves incomplete.**  The sketch names separated-scale and
   cross-window ledgers but defines no incompatibility payloads or consumers
   for their failures.
6. **Exact constant mismatch.**  Lean proves an integer 118-bit floor; nodes
   [22]--[24] use `118.108581006...` and its dependent density constants.
7. **Cold consumer not closed.**  The complete F1--F5 and germ-compression
   route remains partially formalized, so it cannot yet discharge the
   negative branch.
8. **Nodes [23] and [24] remain requirements.**  The current finite decision
   stores the overflow contradiction and high-entropy cap rather than proving
   them.

### Required cleanup

1. Replace the sketch's statement that its three outputs are already an
   "exhaustive scan" by a precise distinction between the implemented
   two-constructor runner and the still-needed application three-way wrapper.
2. Define hot/cold at the weighted window-and-scale level, not through the
   current Boolean `P13HotColdInterface`; select one canonical first failed
   scale so every window is counted exactly once.
3. Register separate typed payloads for ratio underpayment, first emptying,
   scale incompatibility, and cross-window incompatibility.  These outcomes
   do not currently share one proved consumer trigger.
4. Keep the repair branch unnumbered if original node numbering is to remain
   authoritative; do not use node [160]'s Boolean package as its formal
   implementation.

### Advisory

- The conditional-fibre invariant is preferable to an omitted Boolean vector:
  it retains the multiplicities responsible for a rate above 91 bits.
- Preserve `SequentialRatioFailureHandoff` as an arithmetic route.  Add a
  distinct graph-reflection route rather than weakening its honest contract.

## FAIL disposition

- **Exact obligation returned to the repair loop:** construct, from one exact
  selected window, one exact separated scale, and the verified node-[21]
  predecessor, a nonempty finite graph-owned carrier and 91 predicates; prove
  their relation to the safe/flat rows; then prove a total application wrapper
  whose four semantic exits are paying/nonempty, first underpayment, first
  emptying, and incompatibility.
- **Negated residual:** failure to construct or reflect the carrier is not a
  cold window.  It is a distinct finite interface residual requiring its own
  producer or level-3 route.  A constructed carrier's first underpayment or
  first emptying is the later weighted cold residual.
- **Methodology re-entry:** level-2 invariant construction and both-sides test;
  then level-3 interface review for the graph-reflection route.
- **Required next proof:** an exact producer/consumer contract from weighted
  failure to the first graph-semantic cold classification, with S-Def,
  S-Pers, S-Det, S-Rout, and S-Trig; independently, a complete-ledger bridge to
  labelled state counting over the separated scale/window schedule.
- **Complete audit rerun after repair:** no.  The current artifact remains at
  FAIL and blocks manuscript merge or green status for nodes [22]--[24].

## Final verdict

The weighted conditional-fibre idea successfully removes the false
coordinatewise-to-Boolean-cube implication and is the correct local accounting
primitive.  It is not yet a proved manuscript handoff.  The statement/handoff
repair fails only at the graph-semantic producer and route boundaries, while
the full density closure additionally fails at scale aggregation,
cross-window state counting, the exact constant, and the still-open cold
consumer.  Node [21] may remain verified; the weighted connector and nodes
[22]--[24] must remain frozen/open until those obligations are discharged.
