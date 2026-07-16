# Red-team audit: nodes 22--24 window-density realization

## Baseline

- Repair sketch: `nodes_22_24_window_density_realization.audit.md`.
- Original manuscript audit-start SHA-256:
  `6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`.
- Failed node and claim: nodes `[22]`--`[24]`, expanded by
  `[145]`--`[157]`; the missing implication is from the node-`[21]`
  barrier counts to a graph-owned state family, simultaneous Boolean
  realization, commuting cross-window gluing, and finally an exact packing
  ceiling `U13`.
- Methodology consulted: admission and the both-sides test; bookkeeping versus
  new theorems; finite-label design; quantitative first failure; compression;
  CT6, CT7, CT10, CT15 contracts; the level-2/3 repair protocol; scope audit.
- Implicated manuscript material consulted: Part I nodes `[19]`--`[25]`, Part
  XI nodes `[145]`--`[157]`, the detailed dependency table, the complete
  window-entropy/cold-germ section, and the exact remainder residual.
- Current verdict: **FAIL**.

The generic finite-filtration, graph-corridor, and target-defect handoff
prototypes compile.  Compilation verifies the contracts they actually state;
it does not fill the graph-semantic producers or consumers listed below.

## Provenance matrix

| Used fact | Producer | Earlier on this path? | Independent of defect? | Verdict |
|---|---|---:|---:|---|
| selected maximum induced-`P13` packing | CT12 / node `[17]` | yes | yes | available |
| 399 legal labels and fixed compatibility rows | node `[18]` / CT10 | yes | yes | available |
| 91 barrier indices, exact safe/flat counts | node `[21]` / `CT10P13MultiScaleCurvature` | yes | yes | available |
| `2^118 * flatProduct < safeProduct` | node `[21]` certificate | yes | yes | available |
| actual attachment states | `P13ActualAttachmentResponse` | yes | yes | available, but only actual outside vertices and 13 adjacency coordinates |
| graph-owned 91-barrier completion states | none | no | n/a | blocking absence |
| separated dyadic-scale schedule | none | no | n/a | blocking absence |
| simultaneous realization on one window | none | no | n/a | blocking absence |
| commuting product across packed windows | none | no | n/a | blocking absence |
| hot-window cost proportional to `log n` | would require the previous two rows and a scale schedule | no | no | blocking absence |
| ambient-cubic filtering and 15/13 arithmetic | nodes `[151]`--`[152]` / `InducedPathColdLedger` | yes | yes | available |
| constant-size cold corridor state exact for all contexts | none | no | n/a | blocking absence |
| graph-owned promotion from `ColdStructuralGerm` to `ColdBoundedGerm` | none | no | n/a | blocking absence |
| bare `TargetDefective` | literal distinguishing context | yes | yes | available only as residual, not closure |
| exact `U13` and `p13 <= U13` | none | no | n/a | blocking absence |

No later curvature-rank or node-`[132]` fact repairs these rows.  Node `[132]`
is the blocked-pair capacity-token route in Part X and explicitly consumes
literal pair counts, not Boolean realization.

## Quantifier attack

| Claim | Literal quantified form | Smallest countermodel | Result |
|---|---|---|---|
| coordinate activity implies a Boolean cube | `(forall i, exists s, response s i = b)` is used as `(forall assignment, exists s, response s = assignment)` | two coordinates and response set `{00,11}` | false; `01` and `10` are omitted |
| locally hot windows imply a global product | each projection of a global state family realizes both bits, hence all tuples are globally realized | two windows with admissible global states `{00,11}` | false; both local projections are hot, while the global product has only two of four tuples |
| a complete sequential ledger pays entropy | step inequalities alone force a non-vacuous terminal family and a graph-state lower bound | one initial state; first barrier rejects it; arbitrary positive safe/flat weights | false; every step can pay with terminal cardinality zero |
| first ratio failure is a CT6/CT7/CT10 structural witness | `flat*before < safe*after` implies target distinction, refinement, or cold incidence | one inert state, accepting predicate, `safe=2`, `flat=1` | false; the inequality contains none of those payload fields |
| finite displayed two-boundary data give a constant exact target type | bounded boundary labels determine response against every outside context | path pieces of distinct lengths `k,l`; choose a long outside path of length `2^m-k` | false; for large `m`, one glued cycle has length `2^m` and the other `2^m+(l-k)`, so exact dyadic response distinguishes them |
| neutral equal-length first failure gives a smaller representative | equal boundary/response data plus a removed coordinate implies existence of a lexicographically smaller piece | one table row whose two representatives are literally the same piece | false; neutrality supplies no smaller representative |
| modular hit gives a realized graph completion | `2^k = L+r+j delta` for some residue hit implies an available `j`-fold homogeneous repetition | take a residue hit requiring `j>0` but an ambient graph with no second copy (`N=0`) | false; arithmetic congruence does not construct repetitions |

Injection-versus-surjection, pairwise-versus-simultaneous realization, rank
versus Boolean cube, representative existence, and context-generator
completeness all fail before node `[24]`.

## Branch and invariant audit

- Positive-side payment: **not established**.  `CompleteLedger.product_le` is
  correct, but it only proves
  `safeProduct * finalCard <= flatProduct * initialCard`.  The repair has no
  theorem that `finalCard > 0`, no graph-owned bound interpreting
  `initialCard/finalCard`, no `log n` scale multiplicity, and no cross-window
  product.  It therefore does not pay the claimed window-entropy account.
- Negative-side bounded witness/consumer: **not established**.  The first
  failing fibre is finite only relative to a caller-supplied state table and
  arbitrary acceptance predicates.  No theorem reflects its inequality to a
  target response, a CT6 `FailureData`, a CT7 representative pair, or a CT10
  datum collection.
- Measurability: generic filtration data are measurable once supplied, but
  the P13 state table and response-derived 91 barrier predicates are not
  constructed from the selected graph.
- Ladder legality: the sequential-ratio invariant is not admitted because its
  two sides do not yet have the claimed accounts/routes.
- Cross-branch leakage: the sketch names target-defect, exit-(4), CT15, CT4,
  CT7, and CT10 consumers without constructing their exact triggers.  The
  manuscript cold branch also treats already excluded target defects as if
  every new defect were already discharged.
- Theorem weakened or assumption added: the current Lean support is honestly
  conditional on raw finite state/predicate inputs.  Promoting it to node
  `[24]` would add precisely the missing graph theorem as caller data.

## CT obligations

| CT instance | Trigger actually required | Unfilled schema / mismatch | Verdict |
|---|---|---|---|
| sequential filtration (new Core profile) | explicit `FinEnum State` and all barrier predicates | P13 graph producer, response reflection, persistence, nonempty terminal semantics, and entropy account absent | sound utility, not an admitted node route |
| CT6 | a branch-indexed failure predicate and exact `FailureData` at the first hit | ratio failure contains only stage, before-list, after-list, and arithmetic inequality | blocking |
| CT7 | two representatives plus a finite context family whose realization semantics are exact | no pair is extracted from a ratio failure; cold table assumes `contextCoverage` | blocking |
| CT10 | an ordered datum collection and registered finite classification/promotion semantics | no datum or promotion follows from a failing ratio; germ table takes the exact candidate table as caller data and proves no coverage | blocking |
| CT15 | graph-owned target-relative coordinates and dependence semantics | a complete cardinality ledger is not target rank and supplies no CT15 coordinate family | blocking |
| CT4 | demands, payers, deterministic charge, capacities | none is constructed by the complete filtration ledger | blocking |
| CT3/G3 | target-complete replacement, internal baseline, internal target-freedom, strict local decrease | all four are fields of `ColdBoundedGerm`/`ColdSilentExchange`, not consequences of `ColdStructuralGerm` | blocking circular producer |

The generic sequential filtration has a decreasing recursive schedule length,
but that measure only terminates the list scan.  It does not certify progress
of any proposed non-closing CT route.

## Reused closed branches

| Handoff | Exact trigger proved | State transported | Consumer dependency cone | Independent | Measure | Verdict |
|---|---:|---:|---|---:|---|---|
| G1 to CT1 | yes, downstream of a supplied `ColdBoundedGerm` hit | yes | existing CT1 | yes | acyclic | locally valid but producer absent |
| G3 to CT3 | yes, downstream of a supplied strong germ | yes | existing replacement/minimality | yes | acyclic | locally valid but assumptions already contain the hard conclusion |
| G2 to `TargetDefectHandoff.Residual` | literal context distinction retained | yes | no admitted closing consumer; wrapper is intentionally not exit-(4) | yes | acyclic | typed residual only, not a closed/reused branch |
| G2 to exit-(4) | no receiver/load/quotient support/charge update | no | not computable | unknown | none | rejected |

`TargetDefective` is not contradictory in the current contracts.  It is an
existential outside-context witness and appears as a surviving alternative in
the rank-drop routes.  The new identity handoff correctly avoids claiming
closure, but it cannot satisfy leaf totality until a real consumer accepts its
payload.  The application adapter also erases the selected distinction into
an existential proposition and recovers one using `Classical.choose`; this is
not a mathematical falsehood, but direct data-preserving routing is required
before provenance can be called executable.

## Leaf totality

| Leaf | Required endpoint | Exact proof/certificate | Practical checker | Verdict |
|---|---|---|---|---|
| all ratios pay | C4 or typed ledger with an already admitted consumer | only product cardinality inequality | polynomial in supplied table | open/blocking |
| first ratio fails | typed CT6/CT7/CT10 payload | no semantic payload theorem | polynomial in supplied table | open/blocking |
| cold F1/G1 | C1 | valid only after a supplied/constructed hit | local | producer open |
| cold high-degree F4 | named surplus handoff | graph producer returns a vertex of degree `>3` | local | consumer and loss accounting not connected here |
| cold quiet return | bounded germ | only `support.length <= |V(G)|`, rejected root length, and subcubic support | may scan an ambient-size path | not constant-local; open |
| cold G2 | typed target-defect consumer | identity residual only | local | no admitted consumer; open |
| cold G3 | C2/CT3 | valid only because the strong input already carries all compression fields | local | promotion/coverage open |
| node `[24]` | exact `U13`, `p13 <= U13` | absent | absent | open/blocking |

The branch is therefore not total.

## Practicality and termination

- Largest verified fixed universes: 91 barriers, 399 labels, 13 literal path
  positions.
- Missing state universe: admissible multi-scale graph completions.  No local
  cardinality bound or canonical enumerator exists.
- Generic sequential checker: linear in barriers times the explicit state
  list, after that list is supplied.
- Actual corridor producer: one canonical deleted-edge return path, bounded
  only by the ambient vertex count.  It does **not** prove the manuscript's
  constant `Q_cold`, `M_cold`, or `D_cold` bounds.
- The manuscript's fixed-state pigeonhole is invalid without exact response
  reflection.  Two-boundary path pieces retain unbounded length information
  for the dyadic target.
- The manuscript overlap proof uses the constant support bound before that
  bound has been established.  With ambient-length corridors, bounded-degree
  graphs can have unboundedly many selected returns sharing a central region.
- The cold increment argument omits availability of the required number of
  homogeneous copies.  Its “bounded dyadic gap” is not uniformly bounded as
  scale grows.
- Hidden global computation: `contextCoverage : forall outside Context, ...`
  is assumed by the strong germ interface; no finite context generator and
  reflection theorem produces it.

## TeX--Lean--framework correspondence

- The detailed manuscript now calls realization, commuting gluing, cold
  corridor coverage, and node `[24]` open.  That is accurate.
- Part I still draws `[23]` as a terminal entropy overflow and `[24]` as an
  asserted density bound; Part XI still draws `[149]`, `[153]`, `[155]`--`[157]`
  as completed outcomes.  The dependency table also presents the density
  invariant as formal content.  These diagrams/tables conflict with the open
  remarks and current Lean frontier.
- `P13ActualAttachmentResponse` constructs only 13 adjacency coordinates;
  `P13HotColdInterface` still requires the raw system as application data;
  `P13SequentialEntropyFiltration` still requires the raw state table and
  predicates.  No Lean declaration proves node `[24]`.
- `InducedPathColdCorridor` is graph-owned but intentionally produces only an
  ambient-size `ColdStructuralGerm`.  There is no promotion to the strong germ
  classifier.
- `P13ColdGermLedger.GermTable` proves exhaustive classification only of its
  supplied candidate type and explicitly makes no graph-level coverage claim.
- `TargetDefectHandoff` is a transfer example for an identity residual, not a
  consumer closure.
- Focused `sorry`/`admit`/`axiom`/`unsafe` search is clean.  The sole flagged
  choice is `Classical.choose` in `P13ColdTargetDefectHandoff`, as discussed
  above.
- Trust base remains Lean/mathlib plus the registered graph interfaces; no new
  external theorem was used.

Focused checks passed:

```text
cd lean
lake build StructuralExhaustion.Core.FiniteSequentialFiltration \
  StructuralExhaustion.Examples.FiniteSequentialFiltration \
  StructuralExhaustion.Graph.InducedPathColdCorridor \
  StructuralExhaustion.Routes.TargetDefectHandoff \
  StructuralExhaustion.Examples.TargetDefectHandoff

cd examples/erdos_64_eg
lake build Erdos64EG.P13SequentialEntropyFiltration \
  Erdos64EG.P13ColdGermLedger \
  Erdos64EG.P13ColdGermTerminalRoutes \
  Erdos64EG.P13ColdTargetDefectHandoff
```

## Findings

### Blocking

1. **First exact failing obligation:** construct, from the selected graph and
   one selected window, a canonical finite multi-scale completion-state family
   and response semantics whose barrier predicates reflect the node-`[21]`
   safe/flat relations.  No such producer exists.
2. Prove an actual positive-side account: non-vacuity/normalization of the
   sequential terminal family, the `log n` scale multiplicity, and either a
   commuting cross-window gluing theorem or a different global charge with no
   product claim.
3. Reflect a first ratio-failing fibre into one exact registered structural
   payload.  Cardinality failure alone does not imply CT6/CT7/CT10 data.
4. Construct constant-local cold types exact for every target-relevant
   context, or replace constant finite-state pumping with a descriptor that
   records the unbounded length/scale datum and has a well-founded consumer.
5. Construct the promotion from graph-owned `ColdStructuralGerm` to an honest
   hit/defect/compression exchange without assuming `locallySmaller`, baseline,
   target-freedom, or context coverage.
6. Supply an admitted consumer for bare target defect.  Exit-(4) is not
   available from the current payload.
7. Derive exact `U13` and `p13 <= U13`; without them node `[24]` and Residual A
   are unavailable.

### Required cleanup

1. Keep Part I/Part XI diagrams, the dependency table, web colors, and theorem
   index synchronized with the open-interface status.  They must not display
   open nodes as terminal/green.
2. Route the G2 distinction as data directly instead of erasing it to `Prop`
   and recovering a witness with `Classical.choose`.
3. Register any new sequential-filtration pattern at framework level only
   after its producer fields, unique consumers, routing proofs, trigger proofs,
   and transfer example are complete.

### Advisory

- Retain `FiniteSequentialFiltration`: it is a useful and correctly verified
  arithmetic utility.  Rename its intended application as support until the
  semantic producers and consumers exist.
- Retain `TargetDefectHandoff`: it accurately documents that target defect is
  a residual, not closure.

## FAIL disposition

- Exact obligation returned to the repair loop: the graph-owned
  completion-state/response producer and its both-sides semantic theorem.
- Negated residual: either the explicit first omitted assignment of a genuine
  graph-owned local system, or the first ratio-failing fibre **together with**
  a proved graph-semantic witness type.  An arithmetic fibre alone is not the
  residual.
- Methodology re-entered: level-2 invariant selection and both-sides test;
  escalate to level 3 only after a reusable producer/consumer interface is
  specified; use level 4 only if nonexpressibility of the unbounded exact
  target response is proved.
- New invariant attempted: sequential safe/flat retention.
- Result: generic telescoping proved, but both graph-semantic routes remain
  unfilled, so the invariant is not admitted.
- Complete audit rerun after prototype compilation: yes.

## Verdict

**FAIL.**  There are blocking and required-cleanup findings, and nodes
`[22]`--`[24]` are not leaf-total.  The source manuscript was not edited by
this audit.
