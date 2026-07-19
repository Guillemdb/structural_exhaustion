---
name: design-structural-exhaustion-proof
description: "Select and chain structural-exhaustion CTs for a new Lean theorem from a manuscript or mathematical proof. Use when mapping proof prose to CT1-CT17, choosing reusable graph or Core profiles and schema-9 executable transition profiles, preserving full accumulated ledgers, auditing local finite universes, or coordinating an end-to-end verified example implementation."
---

# Design a Structural Exhaustion Proof

Translate the supplied mathematics into the smallest practical chain of existing CT contracts. Implement the mathematics stated by the source; do not invent replacement lemmas, global universes, or proof assumptions.

## Establish the formal authority

1. Work from the repository root returned by `git rev-parse --show-toplevel`.
2. Read the exact public theorem and the manuscript section that proves the requested slice.
3. Read `README.md`, `docs/architecture.md`, and the relevant portion of `framework/branch_closure_methodology_extended.tex`.
4. Inspect the compiled registry before choosing a CT:

   ```bash
   jq '.tactics[] | {tacticId, title, capability, capabilityProfiles, terminals, residualKinds}' generated/lean-machines.json
   jq '.transitionFamilies[] | {familyId, sourceTacticId, targetTacticId, profiles}' generated/lean-machines.json
   jq '.transitionProfiles[] | {profileId, familyId, sourceResidualKind, advanceExecutor, authoringBoundary}' generated/lean-machines.json
   ```

5. Treat the compiled Lean declarations and catalog as authoritative. Treat generated prose and diagrams as inspection views.

## Select CTs by mathematical role

Use the manuscript's operation, not superficial vocabulary, to select a tactic.

| CT | Select it for |
|---|---|
| CT1 | A target certificate or a finite search for a realization. |
| CT2 | A minimal-counterexample deletion or exhaustive local replacement step. |
| CT3 | Equality or compression of finite local response vectors across compatible contexts. |
| CT4 | Assigning demands to eligible payers and comparing fibre capacity. |
| CT5 | Locating unsupported local witnesses or aggregating their contributions. |
| CT6 | The first failure in an explicit order, or the ledger obtained when every local check is active. |
| CT7 | Realization in a context, a distinguishing context, or exact neutrality. |
| CT8 | Repeated exact types followed by response comparison and possible removal. |
| CT9 | An overloaded fibre in a finite label partition. |
| CT10 | A direct datum, a missing class, or promotion after exhaustive classification. |
| CT11 | Localizing a negative finite total to one cell. |
| CT12 | Well-founded peeling with restoration and a verified decreasing continuation. |
| CT13 | Tier-one assignment, canonical fallback, reconciliation, and deficit comparison. |
| CT14 | Comparing aggregate lower mass with optional capacities and label multiplicities. |
| CT15 | A target-relative rank drop or a full-rank capacity ledger. |
| CT16 | Exhausting support and comparing the resulting closed code with a target code. |
| CT17 | Bounded compatibility, scale, survivor, and orbit arithmetic. |

Prefer one CT that exactly matches the prose over several CTs that simulate it indirectly.

## Reuse framework profiles first

Search for an existing constructor before defining a raw capability. In particular, inspect:

- `Graph.MinimumDegreeCycle.StaticInput` and
  `Graph.MinimumDegreeCycleRouted` for cycle targets, edge-rooted CT1,
  local-deletion routing, rank-minimal selection, and deletion criticality;
- `Graph.EndpointParityCycle.Profile` for the maximal-path CT6-to-CT9 cycle pipeline;
- `Graph.GreedyColoring` for CT12 peeling, CT4 color choice, and CT1 validation;
- `CT1.TargetCertificateEncoding` and `CT1.TargetEncoding`;
- `CT2.LocalDeletionCapability`, `CT2.Capability.deletionOnly`, and
  `Routes.CT1ToCT2.LocalDeletion.CertificateProfile`;
- `CT3.TargetCompressionContract`;
- `CT4.FunctionalCardinalityProfile`;
- `CT9.ParityCapacityOneSpec`;
- `CT11.NegativeBudgetProfile`;
- `CT12.ListPeeling`;
- `Core.FiniteSaturation.Machine`.
- `Core.FiniteObservedColumn.FourEncoding`, its framework-computed `qCols`, and
  `Core.FiniteStructuralCutState.stateEncodingOfColumnBundle` for finite
  coordinate columns. Applications supply only the four alphabets, observed
  lists, and `Nodup`; never redeclare column bounds, padded code types,
  symbolic cardinalities, their product, or per-column `Fin` encoders.
- `Core.ExactHandoff` for every diagram edge that retains its predecessor
  unchanged while adding local facts. Extend this carrier instead of declaring
  application fields such as `previous` and `previousExact` again.
  Seed exact outputs with `StageNode.exact`, advance canonical dependent chains
  with `StageNode.mapExactStage`, and combine a branch fact with an exact
  predecessor through `StageNode.usingFactAndExactStage`. Use
  `usingExactStage` only when a produced expression has a genuinely separate
  canonical name. The successor must be produced from the retrieved value,
  never from a recomputed copy whose equality proof is ignored.
- `Core.ResidualRefinement.State.StageNode` for a sequential proof prefix on
  one stable carrier, with `require`/`requireStage` for inherited facts and
  `mapYesStage`/`mapNoStage` for one manuscript branch and `mapStages` when
  both existing decision edges immediately produce their next stages. For an
  occurrence schedule use `Ledger.refineStage` and `Ledger.decide`; consume its
  `occurrenceEquiv`/`globallyUniqueCoverage` instead of rebuilding branch
  coverage. Seed occurrence-sensitive provenance with `Ledger.certify` or
  `produceIndexed`, and create item schedules with
  `FiniteResidualLedger.Ledger.ofEnumeration` or `ofMappedEnumeration`.
  For graph supports on a bare schedule, use
  `ResidualSupportRefinement.Profile.viewSchedule`; use
  `FiniteResidualSupportLedger.View.activeOccurrences` for a supported
  subschedule. Never materialize a detached event-value list or introduce an
  application-level empty refinement state.
  Define consumers with `Node.usingFact`, `StageNode.usingFact`, or
  `StageNode.usingStage` so they name only their immediate dependency rather
  than spelling the complete accumulated fact list. A `usingStage` body must
  consume that stage; predecessor-indexed outputs use the exact-stage
  combinators above.
- `Core.Routing.ResidualStage` for every CT edge. Pass the complete accumulated
  ledger to the selected transition profile's public `.advance`, and continue
  only from the returned enabled stage's `.ledgerStage`. A target result is an
  inspection projection, never the next source carrier. Use
  `ResidualStage.extend` and `LedgerExtension` whenever the same-CT ledger gains
  one problem theorem or data value; never create application predecessor or
  equality fields.
  Never replace a returned transition or pointwise execution's `.ledgerStage`
  with `ResidualStage.exact execution`, even when definitionally equal.
- For an ordinary total accumulated-ledger edge, applications must use
  `Routes.Accumulated.advanceCurrent` when the current source is the ledger,
  `Routes.Accumulated.advance` only when a genuine mathematical projection is
  required, and `Routes.Accumulated.OutputLedger` for the identity-current
  output type. Never spell `id`; a genuinely projected output uses
  `ProjectedOutputLedger`. For a
  pointwise edge use `advancePointwise` and `PointwiseOutputLedger`. Never
  re-expand `transition.onLedger`, `EnabledStage`, or the pointwise family in
  an application type alias. A pointwise family of already selected registered
  routes uses `advanceSelectedPointwise` and
  `SelectedPointwiseOutputLedger`.
  For a registered specialized route that has its own public `advance`, name
  its enabled full-ledger output through
  `Core.Routing.CTTransition.OutputLedger`; raw `onLedger` is framework-only.
- `Core.Routing.PointwiseExecutableFamily` for an obligation of the form
  `∀ localIndex, one public CT execution`. Supply the entry, context, and
  trigger pointwise. Do not enumerate, scan, or synthesize a finite universe
  for the index type.
- `Core.Routing.PointwiseTransitionFamily` when that pointwise obligation is
  a family of specialized typed transitions. Supply each semantic transition
  and its current-residual projection, execute with `.advance`, retain the
  aggregate `.ledgerStage`, and read individual evidence via `.localStage`.
  Never replace it with an application `Sigma`/function wrapper.
- `Core.Enumeration.finsetSubtype`, `sigma`, and
  `sigmaOrderedDistinctPairs`, including `subtype_card_eq_filter`,
  `finsetSubtype_card`, `finsetSubtype_sum_val_eq`, and `boolSubtype_card`, for
  local dependent schedules. Applications provide only the owning predicate,
  `Finset`, and fibre enumerations. Use `natCard_eq`, `finset_card_le`,
  `card_le_of_injective`, `length_le_elems_of_nodup`, and the symbolic
  `powersetCard_list_length_le` bridge instead of reinstalling `Fintype`
  instances or enumerating a powerset.
- `Graph.FiniteResidualSupportLedger.View.recognize` and
  `activeOccurrences` for support scans. Preserve literal occurrence identity,
  retrieve accumulated facts with `ResidualRefinement.Ledger.require`, and use
  `activeOccurrences_card_le_occurrences` for the scan bound. Detached
  event-value lists and list-indexed compatibility ledgers are forbidden.
- `Core.PolynomialCheckBudget.zero` for proof-only projections, inherited
  decisions, and zero-copy handoffs. Do not rebuild a zero-check polynomial
  record or its arithmetic proof in an application or CT profile.
- `Core.FiniteBitRelationBarrier.semanticRow`, `SemanticCertificate`,
  `CountCertificate`, and `CertifiedTable` for fixed finite Boolean relation
  matrices. Certify a stored matrix by whole packed-row equality and obtain
  pointwise semantics through `SemanticCertificate.getLsb_eq`. Audit dense
  cached counts in bounded fixed-table modules. Never elaborate a monolithic
  theorem over every source/target entry or raise recursion, heartbeat,
  timeout, or memory limits to make such an audit pass.
- `PolynomialCheckBudget.add`/`branch` and `Counted.bind`/`zip` for composed
  local work. Never re-prove a polynomial envelope for a framework-composed
  schedule.
- `Core.ExactPropertyHandoff` when a node retains its predecessor and adds
  only one proposition. Keep the manuscript node name as a thin alias; never
  create a problem-specific handoff structure for this pattern.
- `Core.SupportStratifiedDetermination` when a quotient is valid on a final
  connected carrier but the proof audits whether it already descends to an
  earlier atom. Keep the two context types and boundary profiles distinct;
  never project carrier universality as atom universality.
- `Canonical.ExampleNodeObligationDescriptor` for Lean-owned property ledgers.
  Web code renders these records and must not independently author proof
  status or obligation counts.

Read the matching external example when one exists: `examples/even_cycle`, `examples/erdos_64_eg`, `examples/greedy_coloring`, or `examples/mantel`.

## Write the execution map

Before editing Lean, record one row for every selected manuscript step:

| Source step | CT/profile | Local input | Author primitives | Expected terminal or residual | Next consumer | Work bound |
|---|---|---|---|---|---|---|

Require every row to identify the exact local universe being inspected. Reject a row that says only "all graphs", "all subgraphs", "all colorings", or another ambient exponential universe.

Use the corresponding registered transition profile only for these compiled
residual flows:

- CT1 avoidance to CT2;
- CT1 C1 terminal to CT12;
- CT2 separating context to CT3;
- CT2 criticality to CT10;
- CT5 charge ledger to CT14;
- CT6 active ledger to CT9;
- CT9 capacity-one overload to CT7;
- CT14 capacity ledger to CT14.

For a compiled profile, invoke its mandatory public `.advance` executor on a
`ResidualStage sourceTactic Ledger` and a projection from the complete ledger
to the current local residual. Continue only via `.ledgerStage`. In example
metadata use `kind := .registeredTransition` and the exact
`transitionProfileId?`; the registry resolves the compiled `advanceExecutor`.

For any other sequence, compose proved theorem outputs through a reusable
Core, CT, or Graph executor that consumes and returns the complete accumulated
ledger. Do not place predecessor, context, ledger, or execution plumbing in an
application. Every direct cross-CT workflow edge must name its framework
executor, and the compiled catalog rejects empty or problem-owned automation.

The following are forbidden: `TacticInterface`, `RouteRule`, `GeneratedRoute`,
compatibility aliases, manual predecessor/equality fields, freshly rewrapped
local residuals, and chaining from a bare target result. Do not recreate these
surfaces under different names.

## Enforce practical local computation

- Build `FinEnum` values from proof-specified local data. Use `Core.OrderedCollection` only when first-hit order is observable and use `Finset` for unordered sums and cardinalities.
- Prefer a supplied certificate over searching for one. Prefer a finite coordinate response with a reflection theorem over deciding the target on glued ambient objects.
- State the exact number of primitive checks. Prove a `Core.PolynomialCheckBudget` or the CT's native work-bound theorem against a declared input size.
- Use only structurally decreasing recursion. For CT12 and finite saturation, expose the decreasing measure consumed by the framework runner.
- Do not enumerate `SimpleGraph V`, every subgraph, every coloring function, or a recursively expanding universe of contexts.
- Keep reference semantics as the proof authority. Add an optimization only with a theorem equating it to the reference result.

If the manuscript's local step is not practical under the current API, generalize the framework contract or graph layer so the local data and work theorem become reusable. Do not hide the issue in application code.

## Implement the selected chain

1. Define one `Core.Problem` and shared contexts.
2. Read and follow each selected `.agents/skills/implement-structural-exhaustion-ctN/SKILL.md` completely.
3. Read and follow `.agents/skills/implement-structural-exhaustion-route/SKILL.md` for every registered transition profile used.
4. Implement only problem-specific primitives in the example package. Put theorem-independent finite machinery in `Core`, graph mathematics in `Graph`, and CT execution semantics in the relevant CT namespace.
5. Invoke the public reference runner. Retain the terminal, typed path, and terminal-indexed outcome together.
6. Prove semantic soundness, totality, the expected terminal, the exact trace, and the local work bound.
7. Add a small concrete fixture that pins execution without serving as a substitute for the general theorem.

Do not leave declarations for later proof stages half-filled. Omit future stages until their manuscript section is selected.

## Completion gate

Finish only when the requested slice:

- contains no admissions, unsafe declarations, caller-authored outcomes, or hidden global solvers;
- compiles through the external package boundary;
- exposes the exact theorem proved, the CT executions used, and their typed traces;
- passes the architecture linter and repository validator;
- has no manual node obligations; and
- describes the current implementation directly without claiming unimplemented manuscript stages.
