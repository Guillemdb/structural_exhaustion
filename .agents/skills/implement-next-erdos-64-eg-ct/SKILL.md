---
name: implement-next-erdos-64-eg-ct
description: "Advance the repository's Erdős--Gyárfás Problem 64 Lean formalization by exactly one structural-exhaustion CT selected from the manuscript's directed residual flow. Use when continuing proofs/erdos_64_eg/erdos_64_proof.tex: reconstruct every incoming and outgoing branch, consume the full accumulated residual ledger, select schema-9 executable transition profiles, identify the first dependency-ready CT block, perform a framework-first ownership audit, keep Erdős code to concrete data and thin instantiations, execute from earlier verified outputs, prove non-Erdős transfer, synchronize TeX--Lean--web evidence, build affected packages, and update the implementation log."
---

# Implement the Next Erdős 64 CT

Advance exactly one CT per invocation. Complete the earliest unfinished CT at
the verified proof frontier and stop; do not scaffold or partially implement a
later CT.

## Establish the authorities

1. Work from `git rev-parse --show-toplevel` and inspect `git status --short`.
   Preserve unrelated worktree changes.
2. Read completely:

   - the preliminary architecture and Chapter 1 proof-flow material in
     `proofs/erdos_64_eg/erdos_64_proof.tex`, followed by every full
     definition and proof cited by the selected dependency row;
   - `examples/erdos_64_eg/Erdos64EG/OfficialStatement.lean`;
   - `examples/erdos_64_eg/Erdos64EG/InternalProblem.lean`;
   - every existing `examples/erdos_64_eg/Erdos64EG/CT*.lean`;
   - `examples/erdos_64_eg/Erdos64EG.lean`, `Tests.lean`, `README.md`, and
     `IMPLEMENTATION_LOG.md`;
   - `examples/erdos_64_eg/Erdos64EG/WebExport.lean`,
     `generated/examples/erdos-64.json`, and the example catalog schemas;
   - `README.md`, `docs/architecture.md`, and the relevant framework
     specification; and
   - `.agents/skills/design-structural-exhaustion-proof/SKILL.md`.

3. Inspect the compiled CT and schema-9 transition catalogs before selecting an API:

   ```bash
   jq '.tactics[] | {tacticId, capability, capabilityProfiles, terminals, residualKinds}' generated/lean-machines.json
   jq '.transitionFamilies[] | {familyId, sourceTacticId, targetTacticId, profiles}' generated/lean-machines.json
   jq '.transitionProfiles[] | {profileId, familyId, sourceResidualKind, advanceExecutor, authoringBoundary}' generated/lean-machines.json
   ```

Treat the manuscript as the mathematical specification, the official Lean
statement as the problem boundary, and compiled Lean declarations as the
implementation authority. Do not infer completion from documentation alone.

## Keep the original diagram topology immutable

Treat `original_erdos_64_proof.tex` as closed and never edit that file. Never
add, rename, split, merge, or remove a diagram node, edge, case, label, join, or
exit. Every public outcome implements an existing directed edge and records its
source node, target node, branch label, producer, and consumer. An internal
helper may refine its payload but cannot create an outcome, new consumer, or
split. Add same-edge support; if unjustified, stop at the last verified node.

Preserve all existing Lean declarations, fixtures, tests, and framework
support while enforcing this topology. If dependency review demotes a node or
shows that code was implemented ahead of its diagram frontier, retain that
code as conditional support and correct only its provenance/status tracking.
Never delete working or partial proof code merely to restore sequential proof
order; deletion requires a separate explicit user instruction.

## Reconstruct the directed residual flow before selecting a CT

Read the proof as a directed graph of local residual transformations, never as
a linear sequence of paragraphs or node numbers. A node consumes the exact
residual accumulated along an incoming branch, performs one local mathematical
move, and returns a terminal conclusion, a handoff residual, or a refined
residual for a later node.

Before editing, write a residual-flow ledger for the complete candidate block:

| Incoming branch path | Exact accumulated residual | Local certificate/data inspected | Negated earlier exits retained | Node move | Every outgoing branch | Consumer or terminal |
|---|---|---|---|---|---|---|

Expand every selected node into a complete obligation ledger with a stable task ID:

| Task ID | Verbatim mathematical obligation/property from the original paper | Exact incoming producer | Lean declaration to prove it | Outgoing consumer | Status |
|---|---|---|---|---|---|

Include every asserted object, retained hypothesis, condition, inequality, semantic
equivalence, execution/trace/totality fact, output, terminal implication, and
work bound. Green requires every task from exact green predecessors. Never let
one theorem stand for omitted properties. After demotion retain proved tasks,
mark every unfinished task, and synchronize the web ledger before continuing.

Enforce all of the following:

- Trace every incoming arrow across all proof-diagram panels and dependency
  rows. Record cross-panel handoffs explicitly.
- Treat the incoming residual as the conjunction of the preceding verified
  outputs and branch decisions on that path. Construct it from their Lean
  values; do not restate it as a new assumption.
- Use a fact at a node only if it was proved on every incoming path or is
  carried by the particular incoming edge being executed. Never import a
  theorem available only after the node, on a sibling branch, or after a later
  rejoin.
- Treat a terminal exit as closing only its own branch. Treat a handoff such as
  Type B data as an output routed to its named ledger, not as a contradiction
  and not as a discarded case.
- Audit every outgoing edge, including bounded/no-overload, first-failure,
  target-defect, compression, delocalization, global-support, and handoff
  alternatives. An unrepresented edge means the CT block is incomplete.
- Allow one CT to cover several diagram nodes when those nodes are the
  internal execution flow of the same contract. Implement the entire
  dependency-ready CT block and all of its terminals/residuals; do not stop at
  the first diagram box inside it.

Keep this permanent branch guardrail for the current manuscript: node `[19]`
routes its yes branch to `[20]`, expanded by `[125]`--`[144]`, while its no
branch reaches `[21]`. The near-cubic estimate at `[138]` is an output of the
non-near-cubic branch. It is not an input to `[125]`--`[137]`. The three
terminal forms of Part X are a sparse exit, a Type B handoff, or the derived
near-cubic spine; account for all three before following the surviving spine.

Distinguish local execution from later aggregate accounting. First classify
each proof-selected local residual and establish exact disjoint ledgers; only
then apply the manuscript's finite sums or capacity comparisons. Never replace
a missing local response, blocker, transition input, or certificate with a global bound.
Conversely, do not demand a global estimate while implementing a node whose
contract only classifies a supplied local residual.

For quotient, rank, context, and suppression branches, carry proof-selected
certificates:

- Let a rank-drop residual contain or logically unpack to its concrete
  determination certificate: determined coordinate, finite dependency
  subfamily, connected support, quotient proposal, and declared support data.
- Distinguish a quotient proposal from an admissible quotient. Check boundary
  profile and target response first; call the quotient admissible only after
  those obligations and the manuscript's representative condition hold.
- Send context failure with one concrete distinguishing context or response
  certificate. Send context neutrality with its proved semantic property.
  Never enumerate an ambient context universe.
- Consume proof-carrying paths and suppression cycles chosen by the preceding
  minimality theorem. Check their finite edge lists; never search all paths or
  cycles merely to obtain a canonical witness.

If the flow lacks an input needed by a consumer, identify the exact missing
definition or lemma, its intended producer node, its consumer node, and the
fields of the missing residual. Correct local bookkeeping when the manuscript
strategy determines those fields. Do not invent a new estimate, assume a
downstream conclusion, or vaguely report that a global theorem is missing.

## Find the verified frontier

Use Chapter 1's proof flow, not CT numbering, to choose the next work item.
Read the architecture load path, the eleven parts under
`Proof-dependency diagram`, and the `Detailed dependency table`. Follow diagram
arrows and table prerequisites; node numbers alone are not a topological order
across branch continuations. Then read the full manuscript definitions and
proofs cited by the first candidate row.
Enforce a green-predecessor gate from the compiled node-status map and every actual incoming diagram edge, including branch joins: yellow, white, and declared-frontier predecessors block selection and editing. Never substitute a later theorem, sibling-branch fact, or author premise for a predecessor output. Internally order a multi-node CT block so every node consumes earlier green outputs, and publish it only when all its nodes are green and the prefix compiles end to end.

Audit each existing Erdős stage against its Lean declarations. Count a stage
as unconditionally verified only when all of the following hold:

- the Erdős-specific input is constructed from `OfficialStatement`,
  `Internal.problem`, and already proved earlier-stage outputs;
- all manuscript data and semantic bridges required by the CT are defined and
  proved in Lean;
- the public framework runner is actually executed;
- its terminal or residual, typed trace, semantic soundness, totality, and
  practical work bound are proved; and
- an exported theorem states the corresponding manuscript claim without
  accepting that claim, a CT outcome, or an uninstantiated author contract as
  a premise.

A file, import, abbreviation, generic wrapper, parameterized capability, or
caller-supplied contract is not by itself a completed Erdős stage. If an
earlier stage fails this audit, that stage remains the frontier even when a
later-numbered CT file exists.

Select the first dependency-ready manuscript stage that fails the audit; that
stage is the complete dependency-ready CT block, including every diagram node
and outgoing residual covered by the contract. Write an execution-map row only
after completing the residual-flow ledger:

| Manuscript labels and nodes | Incoming branch path | Exact prior Lean residual | CT/profile | Concrete local input/certificate | All outputs and exits | Next consumers | Work bound |
|---|---|---|---|---|---|---|---|

Map its mathematical operation to one CT using
`design-structural-exhaustion-proof`. Read the selected
`.agents/skills/implement-structural-exhaustion-ctN/SKILL.md` completely. If
the exact compiled flow is a registered transition profile, also read
`.agents/skills/implement-structural-exhaustion-route/SKILL.md`; otherwise
compose proved outputs directly.

## Pass the framework-ownership gate before editing Erdős code

Classify every planned declaration in the execution-map row before choosing a
file. Use the most general valid owner:

| Declaration depends on | Required owner |
|---|---|
| Only `Core.Problem`, branch/minimal contexts, finite collections, ranks, or generic predicates | `lean/StructuralExhaustion/Core` |
| One CT's specification, capability, runner, result, trace, or semantic theorem | That CT namespace |
| A residual-to-consumer transformation, context transport, trigger construction, or executable-transition provenance | `lean/StructuralExhaustion/Routes` |
| Mathlib graph objects and parameters such as a degree threshold, length predicate, boundary type, or graph-local certificate | `lean/StructuralExhaustion/Graph` |
| Power-of-two/Mersenne arithmetic, the pinned official statement, fixed Erdős constants, or concrete manuscript data | `examples/erdos_64_eg` |

Treat compiled framework APIs and their documented composition patterns as a
binding implementation specification. Use the existing ledger,
runner, executable transition, provenance, trace, work-bound, and residual refinement automation
whenever it applies. Never reproduce its state accumulation, transition execution, support
recognition, accounting, or proof composition in Erdős-specific code.

The framework patterns below are mandatory for every new or migrated node:

- Every CT edge consumes
  `Core.Routing.ResidualStage sourceTactic Ledger`, where `Ledger` is the full
  accumulated branch ledger. Select the exact schema-9 profile and invoke its
  mandatory public `.advance` with a projection from that ledger to the current
  local residual. Continue only from the returned enabled stage's
  `.ledgerStage`. A bare target result may be inspected but never chained,
  seeded as a new stage, or substituted for the ledger.
  A returned transition execution must flow through its literal
  `.ledgerStage`; `ResidualStage.exact execution` is forbidden restaging.
- Ordinary accumulated edges use the framework-owned
  `Routes.Accumulated.OutputLedger` type and execute through
  `advanceCurrent` when the ledger itself is the current source, or `advance`
  only for a genuine source projection, whose type is
  `ProjectedOutputLedger`. Identity-current applications never pass `id`.
  Pointwise edges use
  `PointwiseOutputLedger` and `advancePointwise`. Erdős modules must not spell
  `transition.onLedger`, `.EnabledStage`, or a pointwise-family output type.
  For a pointwise family of selected specialized routes, use
  `SelectedPointwiseOutputLedger` and `advanceSelectedPointwise`.
  A non-accumulated registered route names its output with
  `Core.Routing.CTTransition.OutputLedger` and executes only its route-owned
  public `advance`; application code never calls `onLedger`.
- When the same-CT ledger gains one problem theorem or data value, use
  `ResidualStage.extend` and `LedgerExtension`. When the paper requires one
  public CT execution for every local centre, port, or other index, use
  `PointwiseExecutableFamily`; its dependent function is pointwise and must
  not enumerate or scan the index type. If those local executions are
  specialized transition profiles, use `PointwiseTransitionFamily.advance`,
  continue from its `.ledgerStage`, and inspect each exact typed transition
  only through `.localStage`; never create a problem-specific aggregate.
- The following are forbidden: `TacticInterface`, `RouteRule`,
  `GeneratedRoute`, compatibility aliases, manual predecessor/equality
  fields, freshly rewrapped local residuals, and chaining from a bare target
  result. Do not reconstruct these surfaces under different names.

- For non-CT internal bookkeeping that retains an incoming residual unchanged,
  extend
  `Core.ExactHandoff expected`. Never redeclare `previous`, `previousExact`,
  `exactPrevious`, or an equivalent equality bundle in Erdős code.
  If it adds only one proposition, use `Core.ExactPropertyHandoff` and expose
  the manuscript node as a thin alias; do not define another application
  structure.
  Use `StageNode.exact` for the first canonical output,
  `StageNode.mapExactStage` for a canonical dependent successor, and
  `StageNode.usingFactAndExactStage` after an existing decision fact.
  `usingExactStage` is only for a separately named output. Recomputing the
  predecessor/output while ignoring the retrieved stage is forbidden.
- If the node performs no primitive inspection, use
  `Core.PolynomialCheckBudget.zero size`. Never construct a local zero-check
  budget, duplicate its coefficient/degree fields, or discharge its bound with
  application arithmetic.
- If the manuscript localizes a determination from an original atom to a
  larger carrier, use `Core.SupportStratifiedDetermination` and its graph
  specialization. The original and carrier context types, boundary profiles,
  supports, and representatives remain separately indexed. Reusing one
  response system for both interfaces blocks the node.
- If several nodes retain one carrier, express them as
  `Core.ResidualRefinement.State.StageNode`s and retrieve prior certificates
  with `requireStage`. Use `mapYesStage`/`mapNoStage` for one existing diagram
  branch and `mapStages` when both decision edges produce their next stages.
  On a produced occurrence schedule use `Ledger.refineStage` and
  `Ledger.decide`, whose `occurrenceEquiv` retains every literal occurrence
  exactly once. Use `Ledger.certify`/`produceIndexed` for occurrence-dependent
  provenance and `FiniteResidualLedger.Ledger.ofEnumeration` or
  `ofMappedEnumeration` for a local item
  schedule; do not write `initial.add` or raw occurrence records in Erdős code.
  Use `ResidualSupportRefinement.Profile.viewSchedule` for bare support
  projections and `FiniteResidualSupportLedger.View.activeOccurrences` for a
  supported subschedule; do not name a dummy initial state, hand-write an
  `orderedValues.map` ledger, or materialize an event-value list.
  Use `usingFact`/`usingStage` constructors so a node declares only its direct
  predecessor dependency, never the full growing fact-prefix type. The
  `usingStage` body must actually consume its stage; dependent outputs use the
  exact-stage constructors above.
- Build dependent local coordinate schedules with
  `Core.Enumeration.finsetSubtype`, `sigma`, or
  `sigmaOrderedDistinctPairs`; use `subtype_card_eq_filter`,
  `finsetSubtype_card`, `finsetSubtype_sum_val_eq`, and `boolSubtype_card`
  instead of exposing `Fintype` instance conversions in Erdős code. Use
  `natCard_eq`, `finset_card_le`, `card_le_of_injective`,
  `length_le_elems_of_nodup`, and `powersetCard_list_length_le` for symbolic
  capacity arguments; never enumerate a powerset.
- Support scans use occurrence-native
  `FiniteResidualSupportLedger.View.recognize`/`activeOccurrences`, retrieve
  accumulated facts through `ResidualRefinement.Ledger.require`, and bound work
  with `activeOccurrences_card_le_occurrences`. List-indexed compatibility
  ledgers, event materialization, and `FiniteSearch.onList` scans are forbidden
  in the Erdős proof path.
- Fixed finite Boolean relation matrices use
  `Core.FiniteBitRelationBarrier.semanticRow`, `SemanticCertificate`,
  `CountCertificate`, and `CertifiedTable`. Prove compact whole packed-row
  equalities and project pointwise semantics through
  `SemanticCertificate.getLsb_eq`. Split dense cached-count reflection into
  bounded fixed-table modules. Never elaborate a monolithic theorem over
  every source/target entry or raise recursion, heartbeat, timeout, or memory
  limits for certificate checking.
- Compose check bounds through `PolynomialCheckBudget.add`/`branch` and
  `Counted.bind`/`zip`; application-level polynomial-envelope algebra blocks
  the node when one of these combinators applies.

These carriers are internal plumbing, not diagram nodes or edges. Add only the
node's new manuscript-specific fields around them, and obtain inherited facts
through their projections and transport theorems.

Parameterize every declaration. If replacing the target, degree three, path
length, or fixed constants leaves it meaningful, extract it to Core, its CT,
Routes, or Graph before specialization. This covers target bridges, CT
composition, residual/provenance plumbing, graph-local semantics, and bundles
of generic terminals, traces, and consequences.

Search `lean/StructuralExhaustion` and non-Erdős examples before adding code.
If an automation is missing but reusable, implement it once at framework level
with a framework fixture and non-Erdős transfer, then consume it here. Erdős
modules may contain only concrete manuscript data, deciders, fixed arithmetic
or reflection, official bridges, fixtures, export metadata, and thin
instantiations (`abbrev`, direct definitions, or one-line delegations). A local
reimplementation or application namespace used as generic staging blocks the
stage even if it compiles.

## Preserve provenance through the CT chain

Import the preceding Erdős CT module. Start from its exact `.ledgerStage` and
retain that complete carrier through every later CT edge. Build only the
profile's local-residual projection from the preceding terminal-indexed
outcome, trace, or theorem. Add a named provenance theorem when definitional
reduction does not make this connection explicit.

Never replace an earlier output with a fresh assumption that restates it. In
particular, do not make the final slice theorem accept a capability,
`TargetCompressionContract`, response-correctness theorem, terminal, residual,
or manuscript conclusion that the selected stage is supposed to construct.
The theorem may quantify only over the official problem inputs and genuinely
proved outputs of preceding stages.

Use a registered transition only when `transitionProfiles` contains that exact
residual flow. Invoke its compiled public `.advance` executor named by
`advanceExecutor`; continuation is
the enabled output's `.ledgerStage`. In workflow metadata set
`kind := .registeredTransition` and its exact `transitionProfileId?`, allowing
the canonical registry to resolve that executor. For other CT sequences, use
ordinary theorem composition behind a reusable Core/CT/Graph executor that
preserves the full ledger. An Erdős-local handoff wrapper, empty automation
list, bare-result chain, or independently rebuilt branch context blocks the
edge.

For every constructor of the new outcome, state which incoming residual fields
it consumes and which later node receives it. Prove branch-context identity
when two ledgers or estimates are combined: they must concern the same selected
graph, packing, local schedules, and earlier execution outputs. A numerical
identity from another diagram panel is usable only through its proved handoff
on that identical context.

## Translate the complete selected stage

Translate every definition, case split, local lemma, finite datum, and
numerical bound used by the selected manuscript stage. Do not invent a
replacement argument or weaken the manuscript statement to fit an API.

1. Define the problem-specific finite types, local graph objects, inspection
   orders, predicates, and deciders.
2. Prove each executable predicate equivalent to its manuscript proposition.
3. Instantiate an existing reusable profile or the CT capability with concrete
   Erdős data. Define this instantiation; do not leave it as a caller argument.
4. Invoke the public CT runner and preserve its execution result, expected
   terminal or residual, terminal-indexed outcome, and typed trace.
5. Prove the runner's semantic theorem, totality, exact trace or terminal when
   required, and native polynomial work certificate.
6. Derive the manuscript theorem for this stage from prior outputs and the CT
   result.
7. Add small executable fixtures that exercise every intended branch without
   substituting for the general theorem.
8. Export the new stage from `Erdos64EG.lean` and update package tests and
   current-state documentation.

Before declaring the stage complete, replay the residual-flow ledger against
the Lean constructors. Require one typed constructor or proved impossibility
for every outgoing manuscript edge, and require every nonterminal constructor
to appear as an input to its named next consumer or registered transition.

Do not add `sorry`, `admit`, new axioms, unsafe proof escape hatches, opaque
proof surrogates, or declarations reserved for later stages.

## Maintain the bidirectional TeX--Lean--web index

Treat manuscript indexing and the web theorem companion as part of the proof,
not post-processing. A CT stage is incomplete until the TeX source, compiled
Lean descriptor, and generated web artifact describe the same verified
frontier.

Before implementing the stage:

1. Identify the narrowest existing semantic `\label` for every definition,
   lemma, theorem, section, and proof-diagram node used by the stage.
2. Add missing labels directly to
   `proofs/erdos_64_eg/erdos_64_proof.tex`. Use stable mathematical names such
   as `def:...`, `lem:...`, `prop:...`, `thm:...`, or `sec:...`; never put Lean
   declaration names or implementation status in a LaTeX label.
3. If the formalization exposes a genuine ambiguity, missing hypothesis, or
   mathematical error, correct the manuscript statement and its dependents in
   the same invocation. Do not weaken or silently reinterpret the paper to fit
   a Lean API. If the correction is not mathematically justified, leave the
   stage unimplemented and report the discrepancy.
4. Preserve the complete proof-diagram topology from
   `original_erdos_64_proof.tex`. Never add, rename, split, merge, or remove a
   node or edge. A missing proof step blocks implementation until it is proved
   as a lemma or connector on an existing edge.

After the Lean stage is proved, update
`examples/erdos_64_eg/Erdos64EG/WebExport.lean` in the same change:

- Add or extend exactly one workflow stage for the selected manuscript step,
  with its primary declaration, all reader-relevant evidence declarations,
  inbound link automation/evidence, and problem-to-framework interface bindings.
- Every ordinary direct link between distinct CT stages must populate
  `automationDeclarations` with its compiled framework-owned executor; never
  use an Erdős-local wrapper or a `Graph.External` theorem as transition
  automation. A registered transition must leave `automationDeclarations`
  empty: set `kind := .registeredTransition` and the exact
  `transitionProfileId?`, and let the canonical registry resolve the profile's
  public `advanceExecutor`.
- Add or extend the corresponding `ExampleProofStepDescriptor` in
  `erdosManuscript`. Record the stable TeX labels and diagram node IDs, a plain
  explanation, a genuine TeX mathematical statement rather than Lean pretty
  printing, the precise correspondence kind, scope limitations, and the
  practical work bound.
- Publish the node's complete obligation ledger in the web companion. Each
  task must have a stable ID, the original-paper property, proved/partial/
  missing status, exact Lean evidence for proved tasks, and the missing
  producer for unfinished tasks. A status demotion must update this ledger in
  the same change; removing a node from `formalizedNodeIds` alone is invalid.
  Store the records in `erdosManuscript.nodeObligations` using
  `ExampleNodeObligationDescriptor.provedForStep`, `partialForStep`, or
  `missing`. The frontend may render or filter this exported list but may not
  define a competing obligation or color source.
- Classify declarations into `ExampleDeclarationGroup`s by their actual role:
  mathematical definition, semantic theorem, encoding bridge, execution,
  trace audit, soundness/totality, work bound, provenance, framework
  interface, external theorem, or fixture. Explain what every group contributes
  to the manuscript argument.
- Expose every new public Erdős declaration that a reader needs to reconstruct
  the selected stage. If a declaration is intentionally omitted, make it
  private/local or record a concrete justification in the implementation log;
  do not leave unexplained public proof steps hidden from the web index.
- Mark the step `implemented` only after the unconditional stage audit passes.
  Keep the first future step as `next`, with no `stageId` or declaration groups;
  never attach verified declarations to an unimplemented manuscript claim.

Preserve these two-way invariants. For each implemented proof step `p` mapped
to workflow stage `s`, let `D(s)` be the union of the stage primary/evidence
declarations, matching interface-binding declarations, and evidence on links
entering `s`, including each link's resolved automation declarations. The
resolved set is the explicit executor list for an ordinary composition and
the registry-resolved public `advanceExecutor` for a registered transition.
The union of
`p`'s declaration groups must equal `D(s)`: no
missing explanations and no unrelated declarations. Every displayed stage
must map to exactly one proof step. Reuse of one declaration by multiple stages
is allowed only when each stage explains its role independently.

The resulting navigation must work in both directions:

- TeX label or diagram node -> proof step -> workflow stage -> grouped Lean
  declarations; and
- selected Lean declaration -> declaration group and role -> plain/formal
  explanation -> exact TeX label and diagram nodes.

Do not duplicate this correspondence in an ad hoc Markdown table or encode
Lean identifiers into the paper. The Lean-owned `erdosManuscript` descriptor
is the authoritative crosswalk; the semantic labels in the TeX file are its
stable mathematical anchors, and the generated web artifact is its checked
projection.

## Keep computation local and practical

Use only the finite local data specified by the manuscript. Supply explicit
`FinEnum` values, local decision procedures, check counts, and a
`Core.PolynomialCheckBudget` or the CT-native polynomial certificate. Prefer
certificates and finite response coordinates over search.

Do not materialize all `SimpleGraph V`, all subgraphs, all colorings, all
ambient contexts, or any recursively expanding graph universe. Permit
recursion only with a visible structurally decreasing measure. If the current
contract would require global enumeration, fix the reusable local contract
instead of hiding the computation in Erdős application code.

Treat large symbolic finite cardinalities as opaque proof data. Never ask an
Erdős module to synthesize a `Fintype` for a deeply nested state, construct
`Fintype.equivFin` for the whole state, normalize a power/product cardinality,
or prove a client-side `rfl` equality between an expanded cardinal formula and
`Fin`'s bound. Do not raise `maxRecDepth`, heartbeats, or memory limits to make
such elaboration pass.

Use a framework-owned bundled finite encoding carrying, in one value, the
symbolic bound, encoder, injectivity certificate, and exact symbolic-cardinality
certificate. Build it compositionally from component encodings. Define the
client bound by projection from that bundle and consume its certificates by
projection; keep the expanded paper formula behind the framework certificate.
If this bundle or a positive-bound/product certificate is missing, add the
generic Core abstraction and a non-Erdős fixture first. The Erdős file may only
supply its fixed component alphabets and thin profile instantiation.

For D4--D7 or analogous observed-coordinate columns, the mandatory path is
`Core.FiniteObservedColumn.FourEncoding.ofFintype`, its projected column
encoders, its framework-computed `qCols`, and
`Core.FiniteStructuralCutState.stateEncodingOfColumnBundle`. Never define or
propagate `Q_cols` by restating four bounds, four padded-code cardinalities, or
four `Fin` equivalences in an application file.

Treat the returned `ColumnStateFiniteEncoding` as the sole downstream owner of
that factor.  Project `encoding.qCols`, `encoding.finite.bound`,
`encoding.finite.encode`, and `encoding.finite.encode_injective` from the same
value.  A manuscript-facing `Q_cols` name, when unavoidable for indexing, may
only be a reducible alias of `encoding.qCols`; it must never be an independent
definition, theorem argument, structure field, or manually transported
equality.  Keep the expanded product identity behind
`stateEncodingOfColumnBundle_productCard`; do not re-elaborate it in an
application module.

For dependent constructions, use the canonical `FiniteEncoding` sub-bundle
exactly: set a profile's `stateBound` to `encoding.finite.bound`, its encoder to
`encoding.finite.encode`, and its injectivity field to
`encoding.finite.encode_injective`. Define manuscript names such as `Q` as thin
aliases of that same bound projection and derive exchange/support bounds via
`FiniteEncoding` methods. Never insert a second casted encoder, transparent
expanded product, or separately restated `Fin` index; those layers force later
consumers to unfold the whole encoding.

For curvature or response ranks defined by universal functional quotients,
use `CT15.FunctionalAdmissibleRank.Profile.rankProfile`, whose candidate is
literally a carrier-indexed proposal with admissibility and functionality, and
use its inherited attained `targetRank` maximum. Never replace exact-profile
realizations and quotient-image vectors by outside-context Boolean responses
without a two-way semantic equivalence theorem. Never replace this universe by
proof-carrying support candidates without proving code-cofinality in both
directions. Never reinterpret the manuscript rank as the runner's count of
coordinates lacking pairwise identifications; connecting those objects
requires a separate equivalence theorem.

Before accepting a finite-state change, run a single-process, hard-timeout
module check. A silent timeout, recursion-depth failure, or large RSS increase
is an implementation defect: bisect at declaration boundaries and replace the
normalizing/typeclass path with symbolic framework composition. Never solve it
by evaluating, enumerating, or globally expanding the finite universe.

A finite polynomial scan of the actual residual schedule is allowed and should
remain lazy when possible. Never replace local checks by ambient-universe
enumeration or search for a proof object already supplied by the prior branch.

For manuscript packing stages, distinguish maximum cardinality from maximal
saturation. Use `Core.FiniteDisjointPacking`,
`CT12.DisjointPacking`, and `Graph.InducedPathPacking` when applicable. Their
maximum is proof-selected; the executable CT12 loop receives only the
selected list, its iteration count is exactly that list's length, and it is
bounded by the host vertex count. Carry the exact covered/remainder partition
forward. When the manuscript excludes arbitrary finite subgraphs rather than
only induced supports, use `Graph.FiniteObject.InternalSubgraph` and its
generic minimum-degree monotonicity bridge. Do not mark a later
density-dependent claim such as “the remainder is large” complete merely
because its packing-derived freeness clause is already verified.

For finite induced-path attachment algebras, reuse
`Graph.InducedPathAttachment` and
`CT10.ExhaustiveClassification.Profile`. The graph layer owns compact
bit-code/finite-set equivalence, symbolic positive-gap semantics, actual
attachment labels, cycle construction, `Legal`, `Compatible`, `C`, and
`omegaTwo`. The CT10 profile owns accepted-subtype enumeration, exhaustive
execution, typed trace, semantic validity, totality, and the quadratic work
ledger. Count candidate classification itself in the ledger. Put only the
fixed path order, forbidden target predicate, concrete gap kernel, and exact
manuscript constants in the Erdős module. Connect the stage through
`EdgeRootedBoundariedInducedPathPackingAttachmentPrefix` so the CT10 branch
context and actual-label theorem come from the exact preceding packing
prefix. Use symbolic code-to-mathematics lemmas for parametric semantics;
reserve bounded reflection for the fixed finite counts.

## Place reusable changes correctly

Keep concrete data in `examples/erdos_64_eg`, reusable graph results in
`lean/StructuralExhaustion/Graph`, finite machinery in `Core` or its CT, and
compositions in `Routes`. Change a framework contract only for a demonstrated
API design error, then rebuild all consumers. Never put Erdős names or
constants in `Core`. For every non-fixture Erdős declaration, identify the
fixed datum preventing generalization or extract it.

## Require a non-Erdős transfer instantiation

Before finishing, locate a non-Erdős problem instantiation of the selected CT.
It must:

- lives outside `examples/erdos_64_eg` and formalizes a named, standard
  textbook graph theorem;
- supplies concrete problem data to the same public CT/profile used here;
- executes the runner and proves its semantic result, typed trace, and
  practical work bound; and
- builds as an external example package.

When adding or extending a reusable profile, the non-Erdős package must consume
that exact method. A separate adapter is insufficient; extract duplicated
proofs so both examples are thin instantiations.

The generic `CTNAutomationFirst.lean` fixture does not alone satisfy this
problem-transfer requirement. If needed, implement the simplest natural
textbook example and ensure it builds as an external example package. Reuse the
generalized graph/core material; never add global or exponential search.

## Validate and record the completed frontier

Run checks proportional to every touched layer, including:

```bash
make lint
make framework-build
make erdos-example-build
make export
python3 tools/validate_repository.py --root .
python3 -m pytest -q tests/test_repository.py tests/test_example_catalog.py tests/test_web_api.py
make web-frontend-test
git diff --check
```

Also build the qualifying transfer example and run focused tests for every
changed graph, Core, CT, transition, or catalog surface. Regenerate tracked catalog
artifacts only when their Lean export changed, and inspect the resulting diff.

Compile `proofs/erdos_64_eg/erdos_64_proof.tex` after changing labels or
mathematics. Inspect `generated/examples/erdos-64.json` and require:

- every manuscript label and diagram node referenced by `erdosManuscript`
  exists uniquely in the TeX source;
- every referenced label has exactly one fresh rendered manuscript fragment,
  theorem-like fragments include their adjacent proof, and every selected
  figure compiles to a sanitized hashed SVG; preserve optional environment
  titles and `\cref`/`\Cref` casing, and never accept a caption-only or silently
  truncated fallback;
- `explainedDeclarations == displayedDeclarations`;
- no displayed declaration is absent from the proof-step groups and no group
  names a declaration outside its mapped stage; and
- the new stage, plain explanation, formal statement, scope note, work bound,
  and implementation status appear in the generated web detail.

Do not bypass renderer, schema, source-freshness, or coverage failures. Fix the
Lean descriptor, TeX anchor, or export instead of hand-editing generated JSON.

As a final ownership check, inspect the complete Erdős Lean diff alongside
the transfer example. Reject any generic structure, runner wrapper, bridge
transport, transition proof, or graph theorem that appears only in the Erdős
namespace. Confirm that the framework fixture and the external transfer
package compile before compiling the thin Erdős instantiation.

Only after all required checks pass, update
`examples/erdos_64_eg/IMPLEMENTATION_LOG.md`. Keep it a direct current-state
ledger of unconditional verification. Reconcile the whole ledger against the
compiled Lean declarations on every invocation; do not merely append the new
stage. Record:

- the verified manuscript section, theorem labels, and diagram nodes;
- the web proof-step ID, workflow stage ID, correspondence kind, and exact
  displayed-declaration coverage;
- the CT/profile and exact Erdős Lean declarations;
- the provenance chain from the official problem through prior CT outputs;
- the runner, terminal or residual, typed trace, semantic theorem, totality,
  and work-bound declarations;
- the qualifying non-Erdős instantiation and its shared reusable API; and
- the validation commands that passed and the next dependency-ready
  manuscript section, clearly marked as not yet implemented.

Do not list a conditional author interface as an unconditionally verified
stage. Do not write comparisons with older versions or claims about future
proof completion. If validation fails, leave the verified frontier unchanged.

Stop after this CT is implemented, tested, built, exported, and recorded in
TeX, Lean, and the generated web projection. Do not start a second CT. Report
its mapping, both TeX--Lean index directions, and the declarations connecting
it to the preceding output.
