# Erdős 64 Part XI obligation ledger: original nodes [145]--[157]

Authority: `original_erdos_64_proof.tex`, Part XI and
`def:cold-window-ledger` through `thm:cold-branch-quantitative-closure`.
This ledger records properties, not coarse file status.  `proved` means the
named local Lean fact exists; a whole node is green only when every task is
proved and its immediate predecessor payload is constructed from a green node.

## Node [145]: hot/cold window interface after the spine estimate

| Task ID | Original-paper obligation/property | Exact predecessor | Required/current Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| XI-145-01 | Consume the near-cubic node-[21] packing and its exact selected-window order. | [21], no branch of [19] | `VerifiedP13MultiScaleCurvaturePrefix`; `p13SequentialWeightedProfile` | proved | -- |
| XI-145-02 | Define one live hot extension as a complete window package commuting with every already retained package. | XI-145-01 | `P13SequentialCompatibleExtension`; `P13SequentialHotAggregate.commutes` | proved | -- |
| XI-145-03 | Process every packed window in packing order, accepting a compatible extension or rejecting that exact extension at the unchanged aggregate. | XI-145-01/02 | `p13SequentialWeightedLedger`; `Ledger.accept`; `Ledger.reject` | proved | -- |
| XI-145-04 | Define the hot and cold families as the exact disjoint/exhaustive ledger projection. | XI-145-03 | `p13SequentialWeightedHotCount_add_coldCount`; `p13SequentialWeightedColdWindows_window_nodup` | proved | -- |
| XI-145-05 | Retain recoverable simultaneous choices and bound their product by the common skeleton code. | XI-145-02/03 | `localProduct_le_fixedCapacity`; `exactPoweredRate_le_fixedCapacity` | proved | -- |
| XI-145-06 | Use one local extension decision per actual packed window, with no ambient graph/context enumeration. | XI-145-03 | `SequentialCompatibleExtensionLedger.checks_exact` | proved | -- |

Whole-node result: **proved/green**, assuming the compiled node-[21] status
remains green.  Its output is the exact weighted hot/cold ledger, not any
later hot-failure inequality.

## Nodes [146]--[150]: upper Part-XI decisions

| Task ID | Original-paper obligation/property | Exact predecessor | Required/current Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| XI-146-01 | Define `theta`, `tau(theta)=15 theta/(1-13 theta)`, and the strict `theta < 1/78` decision. | [145] | Exact finite/rational decision and reflection | missing | No typed Part-XI density payload currently connects [145] to this decision. |
| XI-146-02 | Prove `tau(theta)<3/13` iff `theta<1/78`, preserving strictness and denominator positivity. | XI-146-01 | Arithmetic equivalence theorem | missing | Exact threshold theorem required. |
| XI-146-03 | Route yes to [147] and no with `theta >= 1/78` to [148]. | XI-146-01/02 | Exhaustive typed outcome | missing | No exact original-edge outcome. |
| XI-147-01 | Consume the yes branch and the already constructed route-8 private-carrier ledger. | [146] yes and the named route-8 ledger | Typed provenance connector | missing | The current repository has route-8 support, but not this exact Part-XI connector. |
| XI-147-02 | Derive the private-carrier collision/contradiction. | XI-147-01 | Closing theorem | missing | Blocked by XI-147-01. |
| XI-148-01 | Consume `theta >= 1/78` and the exact final hot aggregate. | [146] no, [145] | Typed hot-cap input | missing | No typed [146] output. |
| XI-148-02 | Decide whether the live-hot entropy comparison closes, using the simultaneous recoverable product. | XI-148-01 | Exact powered-rate/capacity comparison exists locally | partial | `exactPoweredRate_le_fixedCapacity` proves the safe-side capacity; the exhaustive paper decision and overflow implication are not packaged. |
| XI-148-03 | Route close to [149] and failure, with its exact hot bound, to [150]. | XI-148-02 | Exhaustive typed outcome | missing | No original-edge decision package. |
| XI-149-01 | From hot overflow derive the paper's `P13` density cap and close that branch. | [148] yes | Entropy-to-density theorem on identical aggregate | missing | Requires the completed [148] overflow output. |
| XI-150-01 | Define `C` as the exact cold count from [145]. | [148] no and [145] | `p13SequentialWeightedColdWindows` | proved | The definition exists, but is not yet bundled with an exact [148] predecessor. |
| XI-150-02 | Prove `C >= (theta-theta_win)n-o(n)` from the failed hot comparison. | [148] no | Exact normalized finite inequality/asymptotic bridge | partial | Finite shortfall inequalities exist (`p13SequentialHotBudget_shortfall_le_cold` and exact normalization), but no full typed Part-XI theorem from [148]. |
| XI-150-03 | Prove the two displayed numerical lower bounds at `1/78` and `1/73`. | XI-150-02 | Certified rational arithmetic | missing | Blocked by the full cold-mass theorem. |
| XI-150-04 | Retain the surviving-branch exclusions and the near-cubic spine for [151]. | [144]/[148] no | Typed surviving-cold-branch payload | missing | No single exact node-[150] output currently carries all paper hypotheses. |

## Nodes [151]--[152]: ambient-cubic loss and exact stub excess

| Task ID | Original-paper obligation/property | Exact predecessor | Required/current Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| XI-151-01 | Consume the exact node-[150] cold family and surviving near-cubic branch state. | [150] | `P13Node151AmbientCubicColdHandoff`, `p13Node150To151`, `previousExact`, `coldWindowsExact`, `spine` | proved | -- |
| XI-151-02 | Partition that cold family into ambient-cubic and non-cubic windows. | XI-151-01 cold list | `p13WeightedCold_cubic_nonCubic_length` | proved | -- |
| XI-151-03 | Charge each non-cubic cold window injectively to positive total surplus. | XI-151-02 and [21] surplus bound | `p13WeightedColdNonCubic_length_le_totalSurplus` | proved | -- |
| XI-151-04 | Derive the exact finite square-root form of `all but o(n)` non-cubic loss. | XI-151-03 | `p13WeightedColdNonCubic_length_sq_le_nearCubicBudget` | proved | -- |
| XI-151-05 | Export the retained ambient-cubic cold family to [152]. | XI-151-02 | `p13WeightedColdCubicWindows` | proved | Must be repackaged as an output of the missing XI-151-01 connector. |
| XI-152-01 | Consume the exact ambient-cubic family produced at [151]. | [151] | `P13WeightedColdCubicWindow` | partial | Local type is exact, but whole predecessor is yellow until XI-151-01 is fixed. |
| XI-152-02 | Prove one induced `P13` has degree sum `39`, internal contribution `24`, and exactly `15` external stubs. | XI-152-01 | `InducedPathColdLedger.externalStubs_length_eq_fifteen` and supporting graph arithmetic | proved | -- |
| XI-152-03 | Select the first two transit stubs and exactly the remaining `13` branch-excess stubs in canonical local order. | XI-152-02 | `p13WeightedColdBranchExcessStubs`; `p13WeightedColdBranchExcessStubs_length` | proved | -- |
| XI-152-04 | Form the complete cold schedule without importing hot/unrelated windows or duplicating a cold endpoint. | XI-152-03 | `p13WeightedColdBranchExcessSchedule`; `P13WeightedColdBranchExcessStub.sameWindow` | proved | -- |
| XI-152-05 | Prove `b(S_cold) >= 13 C-o(n)` in exact finite form. | XI-151-03 and XI-152-04 | `p13WeightedColdBranchExcessSchedule_length`; `thirteen_mul_weightedCold_le_branchExcess_add_surplus`; `verifiedP13WeightedColdNearCubicPayment` | proved | Whole-node green remains blocked by the yellow immediate predecessor [151]. |

Whole-node consequence: node [151]'s exact immediate connector and local
arithmetic are now proved.  It remains **yellow** under the exact-predecessor
policy because node [150]'s surviving-branch exclusion obligation is still
yellow upstream at node [144].  Demotion must not erase XI-151-01--05 or
XI-152-02--05.

## Node [153]: stage-major first failure and bounded-germ extraction

| Task ID | Original-paper obligation/property | Exact predecessor | Required/current Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| XI-153-01 | Consume each exact selected node-[152] branch-excess half-edge once. | [152] | `source_mem_node152_branchExcessSchedule`; restricted prefix-package source | partial | Exact local source is proved; whole [152] predecessor is yellow. |
| XI-153-02 | Construct its actual outside component, cyclic successor stub, and lexicographically first simple return corridor. | XI-153-01 | `p13WeightedColdRestrictedComponentSchedule_sources`, `p13RestrictedLexFirstCorridorProfile`, and `restricted_component_lexFirstCorridor` | proved | Every exact-once node-[152] component occurrence uses its actual restricted outside component, genuine cyclic `List.next` successor, and the lexicographically first simple endpoint path. Exact head, last vertex, simplicity, no-earlier-path, and length below the local component cardinality are kernel-checked; the cross-window constructor is unchanged. |
| XI-153-03 | Define the finite structural cut state, `Q_cold`, and bounds `M_cold`, `B_cold`, `D_cold`. | XI-153-02 | structural-cut-state modules and constants | partial | Constants/state exist; the complete paper semantics and overlap use are not all connected. |
| XI-153-04 | At each stage test F1 first, then F2, F3, F4; enter F5 only when all earlier alternatives are negative. | XI-153-02/03 | restricted prefix stages, semantic comparison, F1 handoff, prior-support/D6 stages | partial | Individual local runners exist; a single exhaustive stage-major runner with every exact branch and global ledger exclusion is missing. |
| XI-153-05 | Route F1 to a literal power-of-two cycle. | XI-153-04 F1 | verified F1/dyadic support and certificate consumer | proved | Must be connected through the original [153]->[154]->[155] predecessor chain before [155] can be green. |
| XI-153-06 | Route F2 to one literal distinguishing context/target-defective quotient. | XI-153-04 F2 | repeated-pair `classifyF2`; exact distinction payload | partial | Repeated-pair semantics are implemented; full stage coverage and downstream named-ledger connector are missing. |
| XI-153-07 | Route F3 universal response plus strict smaller representative to compression. | XI-153-04 F3 | `classifyF3`; verified replacement contradiction | partial | Implemented for the repeated structural pair; full first-failure producer is missing. |
| XI-153-08 | Route F4 to the already named Type-B or route-8 handoff, on the identical occurrence. | XI-153-04 F4 | produced-prior/D6 local ledger checks; `P13ProducedPriorSupportLedgerCoverage.CompleteState`, occurrence membership, `outside_all_produced_occurrences`, and the exact `LocalCorridorSurvivor` connector | partial | Aggregation is branch-total relative to the literal ordinary occurrence schedule and node-[84] realization: every ordinary, grouped decorated, and extracted route-8 occurrence is retained. The graph-owned producer of the complete ordinary `[64] -> [65]` schedule and the unconditional node-[84] realization from all actual node-[65]/[108] entries remain missing. The independent pre-node-[24] audit additionally proves a causal obstruction: `[57]` consumes `[24]`, while Part XI is used to establish `[24]`, and the original diagram has no backward edge carrying later `[64]`, `[84]`, or `[108]` occurrences into `[153]`; see `ERDOS_64_NODE_153_PRODUCED_SUPPORT_LEDGER_GAP.md`. |
| XI-153-09 | If the corridor terminates before the state bound, retain the whole actual path, exact run equation, F1/F4 negatives, and support bound. | XI-153-04 F5 terminal | `TerminalF5Support`; `terminalF5Support` | proved | -- |
| XI-153-10 | If a structural state repeats, retain the exact earlier/current prefix pair, span bound, universal F2, negative F3, exact run equation, and F1/F4 negatives. | XI-153-04 F5 repeated | `RepeatedF5Support`; `repeatedF5Support` | proved | -- |
| XI-153-11 | Prove terminal-or-repeated F5 exhaustiveness once F2 distinctions are excluded. | XI-153-09/10 | `terminalSupport_or_repeatedSupport_of_f2_clear` | proved | Kernel audit reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; there is no new or problem-specific axiom. This theorem intentionally stops before germ construction. |
| XI-153-12 | From either F5 support construct the paper's two same-interface representatives, proper atom, boundary-profile equality, exact increment, finite response code/table, reflection, symbolic context coverage, and conditional silent orientation. | XI-153-09 or XI-153-10 | Required graph-owned `ColdBoundedGerm` producer | missing | Exact blocker documented in `ERDOS_64_NODE_153_F5_COLD_BOUNDED_GERM_MISSING_PRODUCER.md`. |
| XI-153-13 | Show every surviving selected half-edge yields exactly one canonical germ incidence after only the named routed losses. | XI-153-04--12 | Incidence producer and exact loss ledger | missing | Blocked by XI-153-08/12 and the branch-total ledger. |
| XI-153-14 | Prove the subcubic per-vertex multiplicity bound `B_cold` and per-germ intersection degree at most `M_cold B_cold`. | XI-153-13 | Graph-local bounded-overlap theorem instantiated on actual supports | missing | Generic bounded-overlap machinery exists; the actual germ-support incidence is not yet produced. |
| XI-153-15 | Greedily extract pairwise vertex-disjoint germs and prove `N_germ >= b/D_cold-o(n)` and the two substitutions through `13C` and `theta-theta_win`. | XI-153-13/14 plus [150]/[152] | Exact finite extraction and asymptotic bridge | missing | Blocked by [150], [152], XI-153-12--14. |
| XI-153-16 | Account for work using only actual corridor stages, local states, response codes, and candidate supports. | XI-153-02--15 | Local check ledger/polynomial budget | partial | Local runners have bounded schedules; no complete node-[153] aggregate work theorem yet. |

The newly proved theorem XI-153-11 advances the exact original F5 edge without
adding a case: with F2 clear, the actual Core run is terminal or a repeated
state with universal F2 and negative F3.  It does **not** prove XI-153-12 and
therefore does not make node [153] green.

## Node [154]: exhaustive bounded-germ G1/G2/G3 classification

| Task ID | Original-paper obligation/property | Exact predecessor | Required/current Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| XI-154-01 | Consume an actual node-[153] `ColdBoundedGerm`, not a caller-authored surrogate. | [153] F5 | Typed producer | missing | Blocked by XI-153-12. |
| XI-154-02 | Separate equal-length germs to the finite same-interface table and orient a nonzero increment for length-changing germs. | XI-154-01 | Increment theorem and table route | missing | Current `classify` accepts `increment != 0`; predecessor does not prove it or route zero. |
| XI-154-03 | Check literal hit first, then scan the exact finite local response codes for the first distinction, otherwise prove response neutrality. | XI-154-01/02 | `ColdBoundedGerm.contextScan`; `ColdBoundedGerm.classify` | proved | Conditional on a supplied germ and nonzero increment. |
| XI-154-04 | G1 retains the actual hit cycle and window offset. | XI-154-03 | `Outcome.g1`; `ColdDyadicHit` | proved | Conditional. |
| XI-154-05 | G2 constructs one literal compatible outside context distinguishing the representatives. | XI-154-03 | `distinctionOfHit`; `Outcome.g2` | proved | Conditional. |
| XI-154-06 | G3 derives target completeness from symbolic coverage and builds the conditional silent exchange only after neutrality. | XI-154-03 | `silentOfAbsent`; `Outcome.g3` | proved | Conditional. |
| XI-154-07 | Prove the three cases exhaustive with a local work/trace bound and no ambient context enumeration. | XI-154-03 | `classify`; `GermTable.classification_terminal`; `classification_trace`; `polynomial` | partial | The one-germ scan is exhaustive; the same-interface/equal-length table and exact predecessor coverage remain missing. |

## Nodes [155]--[157]: original terminal consumers

| Task ID | Original-paper obligation/property | Exact predecessor | Required/current Lean evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|
| XI-155-01 | Consume the exact G1 constructor produced by [154]. | [154] G1 | Typed connector | missing | Existing same-window/F1 evidence does not replace the immediate [154] predecessor. |
| XI-155-02 | Execute the supplied-cycle CT1 on the identical graph and prove C1, trace, one check, and contradiction with target avoidance. | XI-155-01 | `g1Run`; `g1_terminal`; `g1_trace`; `g1_checks`; `g1_impossible` | proved | Conditional on XI-155-01. |
| XI-156-01 | Consume the exact G2 distinction from [154]. | [154] G2 | Typed connector | missing | Blocked by XI-154-01. |
| XI-156-02 | Convert that literal distinction to the target-defective quotient on the same atom/replacement/context. | XI-156-01 | `g2TargetDefect`; `TargetDefectResidual` | proved | Conditional. |
| XI-156-03 | Route the defect to the exact named sparse-exit or exit-(4) ledger (or an already named handoff where the original prose permits it), preserving occurrence provenance. | XI-156-02 | Existing-edge ledger connector | missing | Current code retains a generic target-defect residual only. |
| XI-157-01 | Consume the exact G3 silent exchange from [154]. | [154] G3 | Typed connector | missing | Blocked by XI-154-01. |
| XI-157-02 | Build and execute the proper-support CT3 compression; prove terminal, trace, one check, totality, and minimality contradiction. | XI-157-01 | `g3Compression`; `g3Run`; `g3_terminal`; `g3_trace`; `g3_checks`; `g3_total`; `g3_impossible` | proved | Conditional. |
| XI-157-03 | Consume every equal-length/short-exception same-interface table row and route realizing, distinguishing, handoff, and neutral rows exactly as the paper states. | [154] zero-increment/table route | Concrete finite table with semantic coverage and row consumer | missing | Current `GermTable` assumes every supplied row is length-changing and does not implement the paper's equal-length table. |
| XI-157-04 | For a neutral table row, construct a genuinely smaller proper representative rather than assuming it. | XI-157-03 neutral | Proper-support compression producer | missing | This is not implied by response neutrality alone in the current code. |

Whole-node result: [155] must remain **yellow** despite its complete conditional
CT1 consumer; [156] and [157] are also yellow.  The local G1/G2/G3 consumers
remain proved tasks and must stay visible in the web obligation view.

## First dependency-ready continuation

The first new local theorem now completed is XI-153-11,
`terminalSupport_or_repeatedSupport_of_f2_clear`.  The next mathematical
producer on the original edge is XI-153-12: construct the neutral
`ColdBoundedGerm` from the actual terminal or repeated F5 support.  This is
blocked by concrete missing graph data listed in the dedicated node-[153]
producer document; it cannot be discharged by relabeling the bounded support
or by accepting a response table from the caller.
