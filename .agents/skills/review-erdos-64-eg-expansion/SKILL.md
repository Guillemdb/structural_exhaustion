---
name: review-erdos-64-eg-expansion
description: "Audit and repair an Erdős--Gyárfás Problem 64 expansion and discharge every partially formalized diagram node before further expansion. Use after implement-next-erdos-64-eg-ct, when any web node is yellow, or when a claimed frontier must be checked for local unconditional Lean provenance, full accumulated residual ledgers, schema-9 executable transitions, agreement with proofs/erdos_64_eg/erdos_64_proof.tex, TeX--Lean--web synchronization, practical local computation, sole-HSS trust, and maximal framework reuse."
---

# Review Erdős 64 Expansion and Clear Partial Nodes

Review the most recently claimed CT stage, repair defects within that stage,
then discharge every yellow diagram node already touched by implemented Lean
evidence. Stop before the next white frontier CT. A clean review means that the
current paper claims, compiled Lean theorems, execution traces, generated proof
view, and implementation ledger describe the same unconditional local results
and that no partially formalized node remains.

## Reject every diagram-topology change

Treat `original_erdos_64_proof.tex` as the immutable authority for the set of
diagram nodes, directed edges, branch labels, joins, and exits. Never add,
rename, split, merge, or delete a node, edge, case, or branch, and never edit
that file. Reject any expansion or repair that represents an implementation
gap, exceptional value, residual subtype, or bookkeeping distinction as new
proof flow.

Review is status- and provenance-correcting, not code-destructive. Preserve
all existing Lean declarations, fixtures, tests, and reusable framework
support when a node is demoted or found ahead of the dependency frontier.
Track such material as conditional support until its exact predecessors are
green. Never delete proof code to make the dashboard agree with the diagram;
deletion requires a separate explicit user instruction.

Require every public Lean outcome constructor and transition-carried residual to carry an
exact correspondence to one existing directed edge: source node, target node,
branch label, producer theorem, and consumer field. An internal helper type may
refine the payload of an existing edge only if it introduces no public outcome,
new consumer, or additional case split. If the exact existing-edge connector
cannot be proved, keep the affected node yellow and report that implication as
the blocker. Never accept a new node or edge as a manuscript repair.

Permit edits to `proofs/erdos_64_eg/erdos_64_proof.tex` only when they make the
mathematics and the existing handoffs rigorous without changing the topology
of the original diagram. As an explicit review check, compare the node IDs,
directed endpoints, and branch labels in the live diagram against
`original_erdos_64_proof.tex`; any difference fails the review.

## Enforce the no-yellow gate

Treat every yellow node as blocking unfinished work. Never start or review a
later white frontier while an implemented proof step still gives an earlier or
cross-branch node only partial coverage.

Do not implement the next CT during this review. Finish the current node-local
audit and clear the yellow set first.

Compute the yellow set from the compiled manuscript descriptor before the
audit and after every repair. A node is yellow exactly when an implemented
proof step cites it but it is absent from `formalizedNodeIds`. Iterate until
that set is empty.

Judge completeness locally, never from the status of the whole conjecture or
of successor nodes. A node is green exactly when Lean:

1. consumes every incoming branch condition and the exact dependent residual
   produced by its immediate predecessor nodes on the same graph/context;
2. defines every mathematical object and finite local datum asserted in that
   node;
3. executes the applicable framework CT and registered transition profile when the node is
   computational, retaining trace, semantics, totality, and work bounds;
4. proves the node's complete conclusion and every output field promised to
   its outgoing edges; and
5. uses no caller assumption that restates the node's conclusion.

The consumers of those outputs and the final theorem may remain unfinished.
For a terminal node, prove only its exact closing implication from the incoming
branch; do not require the other branch or the global theorem. Definitional and
bookkeeping nodes still require an explicit Lean definition or theorem that
realizes their full local contract.

Treat each diagram node as an obligation ledger, never as one coarse status
bit. Before reviewing or implementing it, extract every distinct assertion and
property established by the original paper: incoming provenance, defined
objects, hypotheses retained on each branch, numerical inequalities, semantic
claims, finite executions, outgoing payload fields, terminal implications,
and local work bounds. Give every obligation a stable task ID.
This complete obligation ledger must include every asserted object and every
unfinished task. Removing a node from `formalizedNodeIds` alone is never a
valid demotion.

For every touched node, maintain this complete contract table:

| Task ID | Original-paper obligation/property | Exact predecessor output/branch | Required local Lean theorem or run | Current evidence | Status | Missing producer or resolution |
|---|---|---|---|---|---|---|

Statuses are `proved`, `partial`, or `missing`. A node is green only when every
task is `proved` and every proof consumes a green exact predecessor. One proved
subclaim never promotes the whole node. When any node is demoted, immediately
populate or update its full task ledger, including what remains proved, and
publish that ledger in the web companion before continuing. Never represent a
demotion only by deleting the node from `formalizedNodeIds`.

Before declaring a mathematical implication missing, reconstruct every
incoming path to that node from the Chapter 1 diagrams. Track properties as
typed branch-local residual fields. Check whether similarly named objects on
different branches carry different predicates, and whether a join node
explicitly transports the needed property. Never import a property from a
mutually exclusive branch, a later node, or a same-named object with a
different residual type. Conversely, do not report a gap if one actual
incoming branch already supplies the exact field: connect that predecessor
output to the consumer in Lean.

Repair the missing obligation using the manuscript's stated mathematics. Add
the node to `formalizedNodeIds` only after its row passes the unconditional,
practicality, trust, ownership, and synchronization audits below. Do not make a
node white by deleting an accurate manuscript reference, merge it into a broad
"official statement" mapping, or call related supporting declarations a full
implementation. Correct a genuinely erroneous reference, but map its evidence
to the exact nodes it proves. If a manuscript implication is actually absent,
keep the proof frontier blocked there and report the precise gap instead of
advancing.

## Establish the review authority

1. Work from `git rev-parse --show-toplevel`; inspect `git status --short` and
   preserve unrelated edits. Treat the current declarations and claimed
   frontier as the audit scope; never assume that every dirty file belongs to
   the expansion round.
2. Read completely:

   - `.agents/skills/implement-next-erdos-64-eg-ct/SKILL.md`;
   - `.agents/skills/design-structural-exhaustion-proof/SKILL.md`;
   - the selected `implement-structural-exhaustion-ctN/SKILL.md` and, when a
     registered transition profile is used,
     `implement-structural-exhaustion-route/SKILL.md`;
   - the preliminary architecture, all Chapter 1 proof-flow diagrams, the
     detailed dependency row, and every cited definition and proof in
     `proofs/erdos_64_eg/erdos_64_proof.tex`;
   - `OfficialStatement.lean`, `InternalProblem.lean`, every Erdős `CT*.lean`,
     `Erdos64EG.lean`, `Tests.lean`, `WebExport.lean`, `README.md`, and
     `IMPLEMENTATION_LOG.md` under `examples/erdos_64_eg`; and
   - every changed or consumed declaration in `Core`, the selected CT,
     `Routes`, and `Graph`, plus the non-Erdős transfer example.

3. Inspect the compiled authorities rather than trusting prose summaries:

   ```bash
   jq '.tactics[] | {tacticId, capability, capabilityProfiles, terminals, residualKinds}' generated/lean-machines.json
   jq '.transitionFamilies[] | {familyId, sourceTacticId, targetTacticId, profiles}' generated/lean-machines.json
   jq '.transitionProfiles[] | {profileId, familyId, sourceResidualKind, advanceExecutor, authoringBoundary}' generated/lean-machines.json
   jq '.example.manuscript' generated/examples/erdos-64.json
   ```

The manuscript specifies the mathematics, the official Lean statement fixes
the problem boundary, and kernel-checked declarations determine what has
actually been proved. Generated files are checked projections, never sources
to edit by hand.

## Freeze the exact reviewed blocks

Reconstruct the frontier independently from the theorem-bearing endpoint,
imports, `WebExport.lean`, and the implementation log. Identify the CT added by
the reviewed round and all diagram nodes covered by that single CT, then add
the existing yellow-node debt as separate local blocks. One CT may encompass
several nodes. Follow arrows and prerequisites rather than assuming node-number
order. Do not extend into an untouched white node.

Before repairing anything, write an audit row:

| Manuscript labels and nodes | Previous verified Lean output | CT and transition profile | Concrete local universe | Claimed terminal/residual | Exported theorem | Work bound |
|---|---|---|---|---|---|---|

List every reviewed theorem-level manuscript claim and its exact Lean
declaration. Exclude later white CTs even if the manuscript discusses them
nearby.

## Audit unconditional Lean provenance

Count the stage as unconditionally verified only if every check below passes.

Before the theorem-level checks, reject application-owned expansion of an
ordinary accumulated transition. An Erdős module must name the output with
`Routes.Accumulated.OutputLedger` and use `advanceCurrent` for identity-current
edges; pointwise output must use `PointwiseOutputLedger`. Any application
occurrence of `transition.onLedger`, a hand-spelled `.EnabledStage`, or a
pointwise-family output alias is yellow framework debt.
Reject an explicit `id` argument in `OutputLedger`; a real source projection
must instead be named by `ProjectedOutputLedger` and executed by `advance`.
Selected specialized-route families must use
`SelectedPointwiseOutputLedger` and `advanceSelectedPointwise`.
For a non-accumulated registered profile, require
`Core.Routing.CTTransition.OutputLedger` plus the route's public `advance` and
reject every application-level `onLedger` occurrence.
Also reject `ResidualStage.exact execution` immediately after a transition or
pointwise run; the only accepted onward carrier is that run's `.ledgerStage`.

1. The public endpoint starts from the official object, baseline, and target
   avoidance, or constructs its prior verified context internally. It does not
   accept the new conclusion, a CT outcome, a terminal equality, a transition
   result, a capability, a response-correctness theorem, a survival
   hypothesis, or another author contract that the stage is meant to derive.
2. Every CT edge starts from
   `Core.Routing.ResidualStage sourceTactic Ledger`, where `Ledger` is the full
   accumulated output of the preceding verified edge. For a compiled profile,
   require its public `.advance` and continuation only through the enabled
   stage's `.ledgerStage`. The local target result may be inspected, but it may
   not be chained or freshly wrapped as a source stage.
   For every direct CT-to-CT workflow link, require either a schema-9
   `registeredTransition` with the exact `transitionProfileId` and resolved
   public `advanceExecutor`, or a Core/CT/Graph composition executor that
   preserves the complete ledger. An unresolved link, Erdős-local wrapper,
   copied branch context, copied predecessor equality, manually rebuilt
   ledger, or bare-result chain demotes the target node.
3. Every problem-specific mathematical object, predicate, decider, semantic
   bridge, and finite datum required by the manuscript is defined. Reject
   `True`, `False`, empty universes, opaque booleans, or caller data used as
   placeholders unless an exact theorem proves that they are the manuscript
   semantics.
4. The public framework runner is actually executed. Retain its
   terminal-indexed outcome, typed path and trace, semantic soundness,
   totality, and deterministic or branch-specific facts required by the CT.
   An interface, wrapper, structure, or definition without an execution is not
   a completed stage.
5. If a particular terminal is claimed, derive it from earlier theorems and
   the runner. Do not assume the premise that rules out the other terminals.
   If the mathematics is a dichotomy, export the exhaustive dichotomy rather
   than declaring one branch unconditionally.
6. Check all branches and all nodes belonging to each selected CT or local
   bookkeeping block. Do not mark only the first diagram node implemented and
   do not leave any cited sibling node yellow.

Search the reviewed dependency cone for `sorry`, `admit`, unsafe declarations,
new axioms, and proof surrogates. Use `#print axioms` on the endpoint and the
new semantic theorems. The sole permitted external theorem is the declared
Hegde--Sandeep--Shashank theorem, and only declarations whose proof genuinely
uses that node may inherit it. A noncomputable proof-selected certificate is
acceptable only when its existence is proved and the executable CT scans the
declared local data rather than pretending to compute that choice.

## Check the manuscript mathematics against Lean

For every cited definition, lemma, displayed identity, and case split, compare
hypotheses and conclusions in both directions:

- prove that each executable predicate is equivalent to the manuscript
  predicate;
- verify constants, index ranges, cardinalities, inequality directions,
  strictness, endpoint conventions, and natural-number subtraction;
- verify that every manuscript dependency is provided by an earlier Lean
  output, not by a later-stage fact; and
- verify that the Lean conclusion is neither weaker nor differently scoped.

When Lean exposes a paper error, repair the paper only with mathematics already
kernel-verified in this round. Update the affected definition or theorem,
adjacent proof, formulas, dependency row, and diagram wording consistently,
while preserving stable semantic labels where their mathematical subject is
unchanged. Search every downstream `\cref` and formula for consequences of the
correction. Never weaken or rewrite the paper merely to conceal an unproved
Lean obligation, and never insert Lean declaration names into LaTeX labels or
mathematical prose.

If the manuscript claim cannot be recovered from its stated strategy and
verified mathematics, do not invent a new argument. Keep the public endpoint
at the previous unconditional frontier, mark the reviewed step unimplemented
in the Lean-owned proof crosswalk and current-state ledger, and report the
exact missing mathematical implication.

## Enforce practical structural exhaustion

Audit the computation that the runner performs, not just the theorem's logical
truth.

- Require an explicit finite local universe and observable order where the CT
  needs one.
- Require exact primitive-check accounting and a
  `Core.PolynomialCheckBudget` or CT-native polynomial bound in the declared
  problem size.
- Reject enumeration of all `SimpleGraph V`, all subgraphs, all ambient
  contexts, all colorings, or a recursively expanding frontier.
- Require every recursion to expose a structurally or well-founded decreasing
  measure.
- Restrict `native_decide` to fixed, genuinely small finite tables with a
  proved semantic reflection theorem; never use it to traverse a variable
  graph universe.
- For fixed finite Boolean relation matrices, require
  `Core.FiniteBitRelationBarrier.SemanticCertificate` whole packed-row
  equalities, pointwise semantics through `SemanticCertificate.getLsb_eq`,
  and a `CountCertificate`/`CertifiedTable` for cached counts. Dense reflection
  may be split into bounded fixed-table modules. Reject monolithic
  source/target entrywise elaboration and every attempt to raise recursion,
  heartbeat, timeout, or memory limits.
- Prefer proof-carrying local certificates and finite response coordinates.
  Do not charge a proof-selected witness as if it were an executable global
  search.

If the current API forces impractical computation, fix the reusable contract
and add regression coverage. Do not hide the computation in Erdős-specific
code.

Reject elaboration-time combinatorial expansion as firmly as runtime global
enumeration. In particular, reject graph-specific whole-state `Fintype`
synthesis, whole-state `Fintype.equivFin`, expanded power/product reduction,
client-side `rfl` proofs that normalize symbolic cardinalities, and attempts to
raise recursion, heartbeat, timeout, or memory limits. These are failures even
when the resulting declaration is logically harmless.

Require large finite states to use the framework's bundled symbolic encoding:
the bound, encoder, injectivity proof, positivity facts when needed, and exact
cardinality certificate must be composed in Core and projected by the graph
application. Audit that the Erdős file supplies only fixed local component
encodings and never reconstructs the product plumbing. Validate with one
single-process, hard-timeout focused check; treat a silent timeout or material
RSS blow-up as a yellow-node implementation defect and repair the reusable
framework path before continuing.

When a state has D4--D7 or analogous observed columns, require one
`Core.FiniteObservedColumn.FourEncoding` value. Its `qCols` projection must be
the sole column-product cardinality, and the state must be propagated through
`stateEncodingOfColumnBundle`; any application-local reconstruction of the
four bounds, code-cardinality product, or encoders is a review failure.

Require all later consumers to obtain the column factor from the returned
`ColumnStateFiniteEncoding.qCols`, alongside that same bundle's `finite.bound`,
`finite.encode`, and `finite.encode_injective`. Reject application structures,
arguments, or equalities that separately carry `Q_cols`, and reject
application-level re-elaboration of the expanded product formula. A retained
manuscript-facing name is acceptable only as a reducible projection alias.

Audit dependent field alignment syntactically. A corridor/profile must use one
canonical `FiniteEncoding` projection for all three fields:
`encoding.finite.bound`, `encoding.finite.encode`, and
`encoding.finite.encode_injective`. Reject a second casted encoder, client-side
expanded product, or independently restated `Fin` index. Manuscript-facing
names may alias `encoding.finite.bound`; derived allowances and positivity must
come from `FiniteEncoding` methods on that same sub-bundle.

Audit rank definitions extensionally. If the paper takes a maximum over
subfamilies surviving every functional admissible quotient, require the exact
`CT15.FunctionalAdmissibleRank.Profile.rankProfile.targetRank` object and its
attained-family theorem. Verify that the candidate universe is literally
carrier plus proposal plus admissibility plus functionality. Reject raw
outside-context Boolean response as the meaning of a realized quotient-image
vector unless a two-way semantic equivalence is proved. Reject
`SupportStratifiedRank.Candidate` as the authoritative paper universe unless
code-cofinality is proved in both directions. A CT15 coordinate count or
pairwise nonidentification result does not prove equality with that maximum
without an explicit bridge theorem.

## Audit framework ownership and transfer

Treat the framework's public automation and established composition patterns
as binding implementation specifications. Reject an Erdős-local reconstruction
of accumulated ledgers, residual refinement, executable transitions, provenance, support
recognition, CT execution, traces, work accounting, or other reusable plumbing.
If the needed automation is absent, require one general framework implementation
and fixture before the thin problem-specific instantiation. A mathematically
correct node remains yellow while this abstraction debt exists.

Reject repeated exact-edge and zero-work plumbing. Every CT edge must retain
its full `ResidualStage` ledger through public `.advance` and `.ledgerStage`.
When the same CT stage adds one theorem or data value, require
`ResidualStage.extend` and `LedgerExtension`. For a manuscript obligation
`∀ localIndex, one public CT execution`, require
`PointwiseExecutableFamily`; reject any enumeration, list, scan, or synthesized
finite universe for that index. When every index carries a specialized
transition certificate, require `PointwiseTransitionFamily.advance`, its
target-labelled `.ledgerStage`, and `.localStage`; reject an Erdős-local
`Sigma` or dependent-function aggregate. Every non-CT unchanged predecessor uses the
framework's exact handoff carrier; an Erdős structure declaring its own
predecessor plus equality certificate fails review. Every proof-only
projection or inherited decision must use
`Core.PolynomialCheckBudget.zero size`; a locally assembled zero-check record
or arithmetic bound fails review. Verify that extending these generic carriers
does not introduce a diagram outcome and that application fields contain only
the new mathematical payload of the original node.

Reject `TacticInterface`, `RouteRule`, `GeneratedRoute`, compatibility aliases,
manual predecessor/equality fields, freshly rewrapped local residuals, and
chaining from a bare target result. Do not accept renamed equivalents.

Reject manual refinement and finite-instance plumbing. A stable residual
prefix must use `Core.ResidualRefinement.State.StageNode`; exact chains must
use `StageNode.exact`/`mapExactStage`/`usingFactAndExactStage`; existing decision
edges must use its branch-stage combinators (`mapStages` for a two-edge stage
continuation), and occurrence families must use
`Ledger.refineStage`/`Ledger.decide`. Require `occurrenceEquiv` or
`globallyUniqueCoverage` whenever downstream accounting claims an exact
partition. Occurrence-sensitive producers must use
`Ledger.certify`/`produceIndexed`, and enumerated schedules use
`FiniteResidualLedger.Ledger.ofEnumeration`/`ofMappedEnumeration`. A local dependent coordinate family must
use `Core.Enumeration.finsetSubtype`, `sigma`, or
`sigmaOrderedDistinctPairs` and their cardinality/sum bridges, including the
predicate, `Finset`, and Boolean subtype bridges. Repeated `Fintype`
conversions, raw occurrence records, `initial.add` provenance, hand-written
branch coverage, or a new application
polynomial envelope fail framework ownership review.
Reject a bare support schedule wrapped in an Erdős-local empty refinement
state when `Profile.viewSchedule` applies. Require supported subschedules to
use `FiniteResidualSupportLedger.View.activeOccurrences`; reject detached
event-value lists and hand-written `orderedValues.map` support ledgers. Require `natCard_eq`,
`finset_card_le`, `card_le_of_injective`, `length_le_elems_of_nodup`, or
`powersetCard_list_length_le` instead of local finite-instance plumbing; the
last theorem is symbolic and must not be replaced by powerset enumeration.
Reject list-indexed compatibility support scans. Require occurrence-native
`FiniteResidualSupportLedger.View.recognize`, accumulated fact access through
`ResidualRefinement.Ledger.require`, and the framework active-occurrence
cardinality bound.
Reject application nodes that restate the whole accumulated fact list when
`Node.usingFact`, `StageNode.usingFact`, or `StageNode.usingStage` can name the
single immediate dependency.
Reject a `usingStage` producer that binds but ignores its retrieved stage and
recomputes a canonical predecessor or output. Dependent successors must use
the exact-stage constructors, so their output is constructed from the literal
retrieved predecessor and transported by the framework theorem.

Reject support-universe collapse. When an admitted quotient belongs to a final
carrier `X` but a diagram diamond tests descent to an earlier atom `C`, require
`Core.SupportStratifiedDetermination` or its exact graph specialization. Audit
distinct `C`/`X` context types, boundary profiles, coordinate-support
transport, carrier minimality, and representative indexing. Carrier-relative
target-completeness never proves atom-relative universality without an
explicit restriction theorem.

Classify every declaration introduced or materially changed by the round:

| Dependency | Required owner |
|---|---|
| Generic problems, contexts, finite collections, rank, or arithmetic machinery | `Core` |
| One CT's runner, result, residual, trace, or generic semantic theorem | That CT namespace |
| Residual-to-trigger conversion, context transport, or executable-transition provenance | `Routes` |
| Mathlib graph objects parameterized by degree, target predicate, boundary, or local certificate | `Graph` |
| Power-of-two/Mersenne arithmetic, fixed constants, and official bridges | `examples/erdos_64_eg` |

Apply the parameterization test declaration by declaration: if replacing
degree three, path order thirteen, or the power-of-two target leaves the
statement meaningful, extract it to the framework. Erdős files may retain
only concrete data, reflection proofs, thin instantiations, fixtures, export
names, and genuinely problem-specific arithmetic. Do not move Erdős names or
constants into `Core`, and do not introduce framework imports of an example.

Confirm that a named textbook example outside `examples/erdos_64_eg` consumes
the exact new Graph/Core/CT transition profile, executes the same public runner, and
proves its trace, semantics, totality, and practical bound. A generic CT
fixture using an unrelated adapter is insufficient. If the two examples
repeat the same proof shape, extract it and make both applications thin.

Change a core or CT contract only for a demonstrated general API defect, then
rebuild every existing consumer. Difficulty with one Erdős lemma is not an API
defect.

## Reconcile TeX, Lean, web, and the ledger

Treat `Erdos64EG/WebExport.lean` and its `erdosManuscript` descriptor as the
authoritative crosswalk. For every implemented proof step `p` mapped to stage
`s`, let `D(s)` be the union of stage primary/evidence declarations,
interface-binding declarations, and incoming-link evidence including
resolved automation declarations. For a registered transition, require
`kind := .registeredTransition`, its exact `transitionProfileId?`, the
registry-resolved public `advanceExecutor`, and an empty
`automationDeclarations` field. Require the union of `p`'s
`ExampleDeclarationGroup`s to equal `D(s)` exactly.

Keep a web-visible obligation list for every touched node. It must enumerate
all original-paper tasks, mark each task proved/partial/missing, and attach the
Lean declaration groups proving completed tasks. For a demoted node, preserve
completed tasks and state the precise missing producer for each unfinished
task. Require the compiled yellow set and the keys of the remaining-obligation
view to agree exactly. The web may project this ledger, but it may not invent
mathematical obligations independently of the Lean-owned crosswalk.
Require those records to live in
`ExampleManuscriptDescriptor.nodeObligations`. Export validation must connect
every proved task to an implemented proof step citing the same node and must
reject disagreement between a complete ledger and `formalizedNodeIds`.
TypeScript-only obligation records are non-authoritative fallback data, never authority
for a newly touched node.

Verify both navigation directions:

- TeX label or diagram node -> proof step -> workflow stage -> grouped Lean
  declarations; and
- Lean declaration -> declaration group and role -> plain/formal explanation
  -> exact TeX label and nodes.

Require every displayed stage to map to exactly one proof step, every label and
node to exist uniquely, theorem fragments to include their adjacent proof, and
`explainedDeclarations == displayedDeclarations`. Mark a reviewed node green
only after its local unconditional audit passes. Require the compiled yellow
set to be empty before keeping the first future step `next` without a stage ID
or verified declaration group. Regenerate with `make export`; never hand-edit
`generated/examples/erdos-64.json`.

Reconcile all of `IMPLEMENTATION_LOG.md`, rather than appending a success
paragraph. It may list only kernel-checked unconditional claims and must name
the exact prior output, runner, terminal or residual, trace, semantic theorem,
totality theorem, work bound, transfer example, and next frontier. Keep README
and top-level imports consistent with the same endpoint.

## Repair and validate

Fix the root layer first: generic semantics in Core/CT/Routes/Graph, concrete
instantiation in Erdős, mathematical prose in TeX, and finally the Lean-owned
web crosswalk and generated projection. Add regression tests for every defect
found. Repeat the audits until the yellow set is empty; do not advance another
CT.

Run all checks affected by the round, including:

```bash
make lint
make framework-build
make erdos-example-build
make example-build
make export
python3 tools/validate_repository.py --root .
python3 -m pytest -q tests/test_repository.py tests/test_example_catalog.py tests/test_web_api.py tests/test_skills.py
make web-frontend-test
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build/erdos proofs/erdos_64_eg/erdos_64_proof.tex
git diff --check
```

Run focused Lean builds for the selected CT and transfer example before the
full suite. Inspect generated diffs and the final `#print axioms` output. Do
not report a clean review if a required check fails.

Finish with a concise verdict containing: the reviewed labels/nodes and CT,
the unconditional endpoint and provenance chain, any mathematical correction
made to the paper, abstractions moved to framework layers, transfer coverage,
local work bound, TeX--Lean--web coverage, trust result, and validation
commands. If the stage fails, identify the last unconditional endpoint and the
single precise gap; do not describe the failed stage as implemented.
