# Node [153] D4--D7 and F2--F5 dependency-cone red team

## Verdict

**FAIL: node [153] remains yellow.**  The reviewed code now contains useful,
kernel-checked local D4, D5, D6, D7, survivor, and F2/F3 components, but it
does not unconditionally implement the original node-[153] contract.  In
particular, it neither constructs the surviving-corridor input from node [152]
nor executes the complete stage-major F1--F5 runner and the bounded-overlap
extraction

\[
N_{\rm germ}\ge 13C/D_{\rm cold}-o(n).
\]

This verdict supersedes every earlier snapshot in this file.  No reviewed
declaration justifies adding 153 to `formalizedNodeIds`; the generated
manuscript correctly omits it.

## Original-topology audit

The Part XI diagram in `original_erdos_64_proof.tex` has the unchanged edge
sequence

```text
[152] -> [153] -> [154] -> [155]/[156]/[157].
```

The live diagram preserves those node IDs, directed endpoints, and the three
G1/G2/G3 outgoing labels.  F1--F5 are the internal priority cases of original
node [153], not additional diagram vertices.

The current Lean cone nevertheless exposes several public constructors that
do not denote an original edge:

- The review found and removed `PriorPiecePairDecision.degenerate` and
  `MatchedPriorPiecePairDecision.degenerate`.  The earlier-prefix schedule now
  contains only positive stages, membership proves positivity, and
  `PriorPiecePair` and `MatchedPriorPiecePair` are constructed directly.
- The review found, and the parallel D6 cleanup removed,
  `MissingD6SubfamilyProducer`, `MissingD6SubfamilyResidual`, and the
  `missingSubfamilies` field of `D6Complete`.  They encoded implementation
  debt as a public D6 result.  The absent node-[70]/[72]/[73] producers are now
  documented outside Lean proof flow.
- The review found and removed the unused `D7CarrierRelabellingFrontier` and
  its constructor.  They were project-management packaging, not an F1--F5
  result.  The mathematical fixed-code comparison and support theorem remain.
- The public `F4F5MissingProducer` and `F4F5IntegrationFrontier` management
  types were removed.  Their missing implementation producers are recorded
  only as review obligations, not as original proof flow.

Local classifier result types used only inside a finite computation do not by
themselves create diagram branches.  They must remain implementation-local
and must not be exported or consumed as proof-flow alternatives.

## Local contract audit

| Original node-[153] obligation | Exact predecessor required | Current kernel-checked evidence | Missing unconditional producer | Verdict |
|---|---|---|---|---|
| Surviving cold corridor from [152] | The exact selected cold branch after high, surplus, ordinary/decorated Type B, and route-8 incidences have been charged to their existing ledgers | `LocallyClearStage` records an exact D5 no-high result and an exact negative D6 scan at one stage; `LocalCorridorSurvivor` records this for every supplied stage | No theorem constructs `LocalCorridorSurvivor` from [152].  It is a caller-provided universal survival payload.  Its D6 negativity is only relative to the supplied ledger, whose global completeness is unproved. | **FAIL** |
| D4 | Same stage and bounded active carrier | All supported two-role wedges are stored; the Boolean is the literal graph predicate; the scan has fixed bound 108000; the fixed coordinate map is injective | Integration into a complete original state still depends on the missing survivor and full D5--D7 producers | **PASS locally** |
| D5 | Same positive prefix and no-high result produced on that stage | Seven currently available base families have exact graph data, fixed carrier-role labels, exact values, injective fixed codes, and observed-only normalized lists | Seven `Pending` families remain: receiver-entry channel/label, connector band, cross-port theta, silent basin, carrier restriction, and carrier-labelled subcoordinates.  `D5Available` is therefore not the complete original D5 signature. | **FAIL as node input** |
| D6 | The unique complete ordinary/decorated/route-8 ledger inherited from prior branches | `ProducedPriorD6State.event_origin` proves every stored event came from exactly one supplied ordinary, decorated, or route-8 list.  Structural codes retain kind, role label, support mask, and exact value tuple.  The public missing-subfamily residual was removed. | There is no converse theorem that every prior original handoff occurs in the supplied combined ledger, and the absent node-[70]/[72]/[73] families still lack producers.  `D6Complete.endpointOutside` quantifies only over supplied keys. | **FAIL as complete F4 test** |
| D7 structural state | Same stage and 28-role bounded carrier | All five declared families have carrier-local schedules, distinct exact role labels, complete support masks, and bounded embedded path values.  Fixed codes map only the observed local declared-coordinate list and are noduplicated. | The context-dependent target response is deliberately absent from the fixed structural code and must be supplied by F2.  The unused public frontier wrapper was removed during this review. | **PASS locally, conditional globally** |
| F2 | Two actual positive earlier/current prefixes with equal displayed state, on the same corridor | `classifyF2` quantifies over the actual two packed pieces and returns either one proof-selected outside distinction or universal equality.  It does not enumerate contexts.  The positive earlier-stage schedule now constructs the matched pair directly, without a degenerate outcome.  `F2F3StageExchange` also runs CT7 over a supplied finite local response table. | No predecessor connects the matched pair and its full response comparison to the stage-major node-[153] runner.  `F2F3StageExchange` accepts a `ColdBoundedGerm`, which already contains the context-coverage table and strict replacement data and is an F5/[154]-side object, so it is not an unconditional pre-F3 producer. | **FAIL as node execution** |
| F3 | Exact F2-negative plus a prior-produced strictly smaller proper representative | `ProperRepresentativeProposal` requires the actual current atom, actual earlier replacement, boundary-degree equality, internal target-freeness, baseline, and `LexSmaller`; only such a proposal yields compression.  Universal response equality alone never yields F3. | No theorem produces this proposal from the node-[153] earlier/current repeat.  `classifyF3` only classically splits on `Nonempty ProperRepresentativeProposal`; it does not establish existence.  The germ-based adapter accepts all F3 fields from its caller. | **FAIL as node execution; guard is sound** |
| F4 | F1-, F2-, and F3-negative at the same stage, then membership in an already produced Type-B or route-8 support | `D6F4Hit` retains an actual supplied-ledger event and `f4_event_has_produced_origin` recovers its supplied source list | Complete branch-ledger provenance and the priority connector from exact same-stage F2/F3 negatives are absent | **FAIL** |
| F5 and germ extraction | Every stage negative for F1--F4, then terminal corridor or repeated exact state, followed by bounded-overlap extraction | `FiniteExactStateCorridor` proves a terminal/repeated split on a supplied positive schedule and equal structural code | No unconditional complete code/reflection producer, terminal/repeated two-boundary representative, stage-major runner, candidate-germ incidence family, or `D_cold` overlap extraction is executed | **FAIL** |

## Survivor provenance

`SurvivingSubcubicStage` is now only an abbreviation for
`LocallyClearStage`; this correctly avoids a duplicate constructor on
`[152] -> [153]`.  `runSurvivingSubcubicStage` also rewrites by the stored
`d6Exact` equality and uses the actual `D6Complete` payload.

That does **not** make the public endpoint unconditional.  Neither
`LocalCorridorSurvivor` nor its stage payload is constructed from the exact
node-[152] branch.  The caller can supply the universally clear corridor, and
the code proves only consequences of that supplied value.  Moreover, its
negative D6 theorem says only that the current endpoint is outside every
support in the supplied ledger.  Until restricted high incidences and every
ordinary/decorated/route-8 handoff are proved to occur in that ledger, this is
not the manuscript's surviving-corridor conclusion.

## Fixed-code and response audit

The stale claim that D7 starts from a global slot/free-pair schedule is no
longer true for the fixed state.  The current construction:

1. scans the 28-role carrier tuples to recover only locally supported slots;
2. forms pairs only from that observed local slot list;
3. constructs `d7LocalDeclaredCoordinates` from the resulting local slot and
   pair executions; and
4. maps exactly that observed list to `fixedD7Codes`.

D4, D5, and D6 normalization likewise map their actual stored coordinate or
ledger lists; none materializes its full finite alphabet.  `Finset.univ` is
used only for fixed `Fin 13` window offsets, and `native_decide` only proves
small fixed cardinality identities.  No ambient graph, subgraph, context,
Boolean cube, state alphabet, or boundaried-piece universe is enumerated.

The D7 code is intentionally structural:

```text
label + 28-role support mask + bounded embedded role path.
```

`fixedD7Code_eq_components` explicitly stops at those three fields.  Sparse
pair target response against an outside context is omitted and no theorem
infers it from code equality.  F2 is the separate semantic comparison that
must provide either an actual distinguishing outside context or universal
target equality.  This separation is sound and prevents the earlier
coordinatewise-realization error.

## F3 strictness and chronology

The direct prior/current adapter has the correct one-way safety property:
universal target equality does not create compression.  Compression requires
a `ProperRepresentativeProposal` whose replacement is definitionally the
actual earlier piece, whose atom source is the actual current piece, and which
contains a genuine `LexSmaller` proof and all replacement hypotheses.

The chronology is nevertheless incomplete.  The proposal has no producer
from the positive repeated-prefix schedule.  The older germ adapter is not a
repair: `ColdBoundedGerm` already carries `locallySmaller`, target-free and
baseline proofs, a finite context table, and symbolic coverage of every
outside context.  Accepting that object before F2/F3 imports the later F5/germ
payload backwards.  Its CT7 and CT3 executions are valid only conditionally on
that supplied germ.

## D6 provenance audit

The direction actually proved is exact:

```text
stored D6 event -> member of supplied ordinary/decorated/route-8 producer list.
```

No theorem silently upgrades this to the converse.  In particular,
`D6Complete` proves absence only for keys of the supplied ledger, and the
survivor documentation correctly says so.  This is logically honest, but it
is insufficient for original F4.  The missing theorem is the exact converse
coverage of every relevant prior handoff by the single inherited branch
ledger, together with removal of the public missing-subfamily residual.

## `FiniteExactStateCorridor` audit

`Core.FiniteExactStateCorridor.Profile` stores only:

- the supplied ordered stage list;
- a symbolic state bound;
- an injective encoding into `Fin stateBound`; and
- the structural code of each supplied stage.

Its repeated constructor proves only equality of those two structural codes.
The module contains no target predicate, context response, replacement, or
response-reflection field, and its documentation explicitly requires a later
F2 comparison.  Thus the Core pigeonhole runner makes no forbidden implication
from structural equality to semantic response equality.

The runner inspects only `stages.take (Q + 1)` and proves at most `Q + 1`
stage checks.  It does not enumerate the code type.  The node-[153]
earlier-prefix adapter now filters stage zero before matching, proves every
scheduled earlier stage positive, and constructs the two-boundary pair
directly.  No degenerate piece branch remains.

## Trust and validation

The reviewed dependency cone contains no `sorry`, `admit`, new `axiom`, or
`unsafe` declaration.  `#print axioms` on the D5 exact-code reflection, D6
exact-tuple reflection and producer-origin theorem, D7 component reflection,
surviving-stage runner, both F3 closing theorems, CT7 validity, and
`FiniteExactStateCorridor.run_total` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.  No HSS theorem or additional
external axiom enters this local cone.

The focused dependency-cone build passed:

```text
lake build \
  Erdos64EG.P13WeightedColdRestrictedD4D7State \
  Erdos64EG.P13WeightedColdRestrictedPriorSemanticComparison \
  StructuralExhaustion.Core.FiniteExactStateCorridor
```

After all topology cleanups, the positive-stage chain also rebuilt:

```text
lake build \
  Erdos64EG.P13WeightedColdRestrictedPriorStages \
  Erdos64EG.P13WeightedColdRestrictedPriorPiecePair \
  Erdos64EG.P13WeightedColdRestrictedPriorSemanticComparison
```

The final run completed successfully with 8939 jobs; only linter warnings were
reported.  No TeX, web, node-status, or implementation-status change is
authorized by this failed review.

## Last unconditional endpoint and repair order

The last unconditional endpoint in this cone is the collection of local
observed-clause constructions and their conditional same-stage runners, not
original node [153].  A topology-faithful repair must proceed in this order:

1. construct the single complete inherited D6 ledger and prove both producer
   provenance directions;
2. complete the missing D5/D6 original subfamilies; their implementation debt
   must remain outside Lean proof-flow results;
3. construct the globally surviving corridor from [152], with high, surplus,
   Type-B, and route-8 removal proved from existing ledgers;
4. connect the positive earlier-prefix schedule to the actual repeated-state
   producer (the degenerate stage-zero outcomes are already removed);
5. produce the actual earlier/current full response comparison for F2 and the
   genuine prior-produced strict representative for F3;
6. execute F4 only after exact same-stage F2/F3 negatives, and F5 only after
   exhaustive F1--F4 negatives; and
7. construct the candidate germ incidence family and prove the original
   `D_cold` bounded-overlap extraction.

Until all seven connectors are unconditional, node [153] must remain yellow.

## `[152] -> [153]` theorem-only survivor handoff

The original-flow distinction is important.  Node [151] charges a
non-ambient-cubic packed window to global degree surplus.  After node [152], a
high vertex encountered on a selected cold return corridor is not another
node-[151] window loss: in
`def:cold-corridor-first-failure` and
`lem:cold-corridor-first-failure` it must enter the already declared Type-B
handoff support at F4.  The later `o(n)` deletion in
`lem:cold-germ-extraction` therefore needs either occurrence-level payment or
coverage by that produced F4 ledger; center-level surplus alone is not the
claimed deletion theorem.

The restricted-prefix package now exposes an unconditional provenance theorem
showing that its literal source belongs to
`p13WeightedColdBranchExcessSchedule`.  Thus this local corridor construction
does not replace node [152] by a fresh occurrence or an untyped surrogate.

`exists_localCorridorSurvivor_of_branchExclusions` is the strongest connector
currently justified on the existing edge.  Given, at every literal stage,
the manuscript's semantic subcubic exclusion and absence from every support
in the supplied combined ordinary-Type-B/decorated-Type-B/route-8 ledger, it
constructs `LocalCorridorSurvivor`.  The proof reconstructs the exact negative
D5 and D6 runner equations; it does not add a runner outcome, residual, or
topological case.  It also does not use the obsolete coarse-code equality for
repeated states.

This bridge remains conditional for exactly two predecessor reasons.  First,
the graph-owned high result on each actual prefix now maps to a canonical
literal `degree - 3` surplus slot at the identical center, retaining that
center's membership in the prefix support.  This proves center-level coverage
without a graph scan.  It does not prove occurrence-level payment: the surplus
ledger has no corridor-occurrence key, and several selected corridors may
encounter the same high center.  No theorem bounds that multiplicity or routes
each such occurrence to a distinct paid slot.  Second, although the combined produced-prior
ledger records ordinary Type-B, decorated Type-B, and route-8 events and has
exact producer provenance, no branch-level construction supplies the complete
combined ledger and proves the converse coverage of every relevant earlier
handoff.  These are missing producers on the original edge, not new residual
cases.  Consequently this theorem improves the typed `[152] -> [153]` handoff
but does not make node [153] unconditional or green.

The possible replacement by a degree-only congestion lemma has also been
tested and fails for the actual cyclic-successor/BFS corridor rule.  Two long
cycles sharing one degree-four articulation center, with boundary stubs
alternating between the two sides in the declared cyclic order, force every
successor shortest path through that one center.  The number of selected
corridors is unbounded while the center contributes one surplus slot.  A
uniform-depth variant avoids the local F1 completions as well.  These are not
certified against the full target-avoidance/F2/F3 hypotheses, so the precise
remaining obligation is a target-aware F1--F3-negative congestion or produced-
F4 coverage theorem, not a refutation of the surviving branch.  The explicit
path-system audit and the remaining F4 provenance mismatch
are recorded in `ERDOS_64_COLD_CORRIDOR_CONGESTION_ERROR.md` at the project
root.

The focused validation passed:

```text
lake build Erdos64EG.P13WeightedColdRestrictedSurvivorFilter
```

The build completed successfully with 8925 jobs.  The reusable center-level
bridge also passed its focused framework build:

```text
lake build StructuralExhaustion.Graph.SurplusResidualBudget
```
