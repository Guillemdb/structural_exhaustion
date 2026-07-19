# Automation-first CT architecture

## Authority and dependency direction

The compiled Lean environment is the formal authority. JSON, diagrams, and the
manuscript are generated inspection views.

```text
problem definitions + explicit Mathlib finite enumerators
                     ↓
          minimal CT capability
                     ↓
 generic search / computation / theorem library
                     ↓
 predecessor-indexed states and evidence-carrying edges
                     ↓
 exact reference runner + soundness + totality + determinism
                     ↓
 exact CT-labelled residual stage + declared semantic discovery
                     ↓
 typed CT-transition profile + target executable interface
                     ↓
 mandatory `.advance` + accumulated `.ledgerStage`
                     ↓
       compiled-environment catalog exporter
                     ↓
 schemas, diagrams, audit reports, and manuscript figures
```

No generated layer may declare a node, edge, capability field, residual, or
transition that is absent from Lean.

## The minimal capability rule

A tactic capability may provide:

- mathematical types and predicates;
- primitive semantic operators;
- explicit `FinEnum` values fixing deterministic search order;
- decidability for primitive predicates;
- non-definitional instance bridges whose statements are strictly weaker than
  a final tactic result.

It may not provide a completed node implementation, arbitrary closure claim,
completed outcome, consumer-routing data, downstream input, search result, or
case-selection callback. If an output can be obtained by finite search,
verified computation, or a generic theorem, that output belongs to framework
code. Cross-tactic semantic adapters are recorded separately from tactic
capabilities. Such an adapter may discover and extract only the consumer seed
whose meaning depends on the source residual.

The repository linter rejects untyped transition metadata, cross-CT imports in
a producer, admissions, nonconstructive dependencies, and suspicious
whole-result capability fields.

## Mathlib graph specialization

`Graph.FiniteObject` is the graph layer's mathematical object: a Mathlib
`SimpleGraph` paired with the explicit execution order and adjacency decision
procedure required by deterministic search.
`MinimumDegreeCycle.StaticInput` generates CT1 and CT2 from the
minimum-degree/cycle contract. `MinimumDegreeCycleRouted` generates the
edge-rooted CT1 encoding, certificate-to-local-deletion transition profile,
rank-minimal prefix, deletion criticality, and high-degree independence.
`PackedMinimumDegreeCycle` supplies varying-vertex finite graph objects, a
natural-number encoding of lexicographic vertex/edge rank, injective cycle
transport, and the certificate-driven CT2 proper-subgraph closure. Its runner
checks one supplied subgraph and never enumerates graphs or subgraphs. Its
combined prefix also retains a certificate-driven CT3 stage for boundary
degree fibres, universal context response, replacement, and hereditary
uncompressibility. Its boundaried piece is an actual packed Mathlib graph with
an injective finite boundary labelling; a compatible context carries its
outside boundaried graph, gluing operation, and the local degree-preservation
theorem.
Applications retain only their cycle-length arithmetic and public-statement
bridges. The generic CT3 coordinate machine still receives finite local data
through its ordinary specification and capability interfaces. For literal
graph replacement, `Graph.PackedBoundariedGluing` derives the whole-object
decrease, baseline, and target transport from local graph data before calling
`runCertifiedCompression`; no context or graph universe is generated.
`EndpointParityCycle.Profile` builds the reusable maximal-path, CT6,
CT6-to-CT9 transition, CT9, chord-cycle, and CT1-validation pipeline on top. External
applications select these profiles and retain only their genuinely
theorem-specific predicates and fixtures.

`Graph.InducedPath.Profile` represents an induced path by Mathlib's literal
embedding `pathGraph k ↪g G`. The embedding itself certifies injectivity and
adjacency reflection, so certificate-driven CT1 validates one local witness
in constant work and its avoiding path is exactly induced-`P_k`-freeness.
`PackedMinimumDegreeCycle` can append this stage to its existing CT1/CT2/CT3
prefix without changing the selected context.

`CT10.ExhaustiveClassification.Profile` handles exact finite class tables:
the application supplies an explicit candidate universe and decidable
acceptance predicate, while the profile constructs the accepted subtype,
executes CT10 to the exhaustive terminal, and proves its typed trace,
semantic validity, totality, and quadratic work ledger. For induced-path
labels, `Graph.InducedPathAttachment` owns the compact code equivalence,
symbolic gap test, compatibility algebra, and actual cycle certificates.

`Core.FiniteDisjointPacking` separates finite maximum existence from runtime
inspection. It proof-selects a maximum pairwise-disjoint support family and
proves saturation; it does not expose an executable universe of items or
packings. `CT12.DisjointPacking` sends only the selected list through the
well-founded list-peeling runner, proves one iteration per selected item, and
bounds execution by the host vertex count. `Graph.InducedPathPacking`
specializes supports to ranges of Mathlib
embeddings, constructs the induced complement, and proves the complement and
all its induced subgraphs are induced-path-free.

`Graph.FiniteObject.InternalSubgraph` is the graph-level contract for an
arbitrary finite subgraph on an explicit host support. The reusable
minimum-degree monotonicity bridge proves that its induced closure has at
least the same minimum degree, without enumerating subgraphs.

`Core.FiniteResidualLedger` is the persistent branch-state event log.  Its
primary keys are finite producer occurrences rather than event values, so two
equal residual values emitted at different proof steps remain distinct.  The
ledger supports exact singleton emission, tagged append, occurrence
embeddings, restriction, event projections, enumeration-backed schedules, and
dependent certified views. `ofEnumeration` makes a local `FinEnum` the exact
occurrence schedule without another list; `ofMappedEnumeration` additionally
installs the emitted event view while retaining each input as its occurrence.
`ResidualRefinement.Ledger.certify`
and `produceIndexed` install occurrence-sensitive provenance, so duplicate
event values may retain different producer witnesses without application
`initial.add` plumbing.
Later stages enrich the same occurrence identities through those views; they
do not rebuild an ad hoc event list.  `Graph.FiniteResidualSupportLedger`
specializes one such view to declared finite vertex supports.  Its ordered
recognizer returns the exact first producer occurrence and an occurrence-total
absence certificate, with one membership check per recorded occurrence.
Applications define only their concrete event language, support projection,
and proof-carrying emitters.

`Graph.FiniteResidualSupportLedger.View` is the sole support-scan state.
`recognize` retains the literal first occurrence, while `activeOccurrences`
returns the supported occurrence subtype without collapsing equal event
values. Accumulated facts remain available through
`ResidualRefinement.Ledger.require`, and
`activeOccurrences_card_le_occurrences` supplies the linear scan bound. Proof
state is never converted to a detached event-value list.

`Core.ExactHandoff` is the canonical unchanged-edge carrier.  A diagram node
that adds a local property while retaining its incoming residual extends this
proof-indexed structure; the framework stores the predecessor and its equality
with the exact edge value once.  Application structures contain only their new
mathematical payload and use `ExactHandoff.property` when an inherited theorem
must be transported.  This carrier is bookkeeping, not a new proof outcome.
When the next payload type depends on the retained predecessor,
`StageNode.mapExactStage` runs the producer on the retrieved value and
transports its result to the named edge value. `StageNode.exact` seeds a
canonical output, and `usingFactAndExactStage` combines an existing branch
fact with the exact dependent predecessor. `usingExactStage` is reserved for
the uncommon case where the produced expression must be normalized to a
separately named canonical value. Application code must not eliminate the
equality or recompute an available predecessor.

`Core.PolynomialCheckBudget.zero` is the canonical work certificate for such
proof-only projections and inherited decisions.  It fixes a uniform linear
envelope with zero primitive checks, avoiding repeated budget records and
application-level arithmetic proofs.  Executable local scans continue to use
their owning CT or graph profile's actual check count. Composite schedules use
`PolynomialCheckBudget.add` or `branch`; value-producing executions use
`Counted.bind` and `zip`. These combinators retain the check equation and
polynomial envelope, so applications do not repeat complexity algebra.

`Core.Enumeration` owns exact dependent local schedules. `finsetSubtype`
turns an application-owned `Finset` into the canonical local carrier and its
exact cardinality and direct sum bridges remove competing subtype instances.
`subtype_card_eq_filter` and `boolSubtype_card` own predicate and Boolean
fibre counting without exposing `Fintype.card_subtype`. `sigma`
combines a base enumeration with occurrence-dependent fibres, while
`sigmaOrderedDistinctPairs` builds the common centre-plus-unordered-neighbour-
pair schedule with exact cardinality and a uniform polynomial bound. These
constructors inspect only the supplied local carrier and fibres.
The same layer owns the routine cardinal bridges `natCard_eq`,
`finset_card_le`, `card_le_of_injective`, and
`length_le_elems_of_nodup`. `powersetCard_list_length_le` bounds a
duplicate-free list by its symbolic binomial capacity and never materializes
the powerset.

`Core.SupportStratifiedDetermination` is the canonical carrier when a
determination is valid on a final connected support but the proof separately
tests whether it already descends to an earlier atom.  It keeps the two context
types and boundary profiles distinct and owns support inclusion,
connected/minimal carrier evidence, coordinate support, determination,
quotient identification, carrier-relative universality, representative
indexing, the raw quotient restriction, both interface boundary profiles, the
original-interface context audit, and the at-atom/enlarged
branch decision.  Carrier-relative target-completeness is never transported to the atom
without an explicit restriction theorem.

`CT15.CertifiedDeterminationRank` computes the maximum surviving coordinate
family over proof-carrying quotient candidates. Its strict-loss circuit
retains the exact candidate responsible for a collision.
`CT15.SupportStratifiedRank` specializes those candidates so every nontrivial
collision supplies a `Core.SupportStratifiedDetermination.Certificate` with
the same quotient code and named coordinate pair. Use this pair when a rank
drop is followed by the original-context defect/compression/enlargement
diamond; do not reconstruct support after rank extraction.

`Core.FiniteObservedColumn.Encoding` is the canonical finite-coordinate-column
pattern.  From one finite alphabet it owns the duplicate-free observation
bound, padded symbolic code, exact symbolic cardinality, `Fin` equivalence,
injectivity, and observed-list encoder.  A structural state is assembled with
`Core.FiniteStructuralCutState.stateEncodingOfColumns`, which propagates all
column bounds and encoders automatically without enumerating or synthesizing
the product state.  Applications supply only the actual observed lists and
their `Nodup` proofs; they do not redeclare per-column bounds, code spaces,
cardinal formulas, or `Fin` encoders.

The standard four-column case is represented by
`Core.FiniteObservedColumn.FourEncoding`. Its `qCols` field computation is the
single authority for the combined column cardinality, and
`Core.FiniteStructuralCutState.stateEncodingOfColumnBundle` propagates all four
codes into the structural state.  The returned
`ColumnStateFiniteEncoding` retains that same `qCols` projection alongside the
complete bound, encoder, and injectivity certificate. Graph applications
therefore project `encoding.qCols`; they never restate or transport a
`Q_cols` product themselves.

`CT15.AdmissibleQuotient.Profile` also provides the exact
functional-quotient rank layer. `Survives` means label-injectivity on a
declared subfamily under every admissible quotient; `targetRank` is the
attained largest surviving cardinality. The bound is searched only at the
proof level over possible natural-number cardinalities. It does not evaluate
a coordinate powerset, quotient family, or outside-context universe, and it
must not be conflated with the CT15 runner's separate pairwise-dependence
count without an explicit equivalence theorem.

For a quotient already admitted at the same interface, its proof-selected
`PairCircuit` also owns the next context-validity projection pattern.
`ContextDecision` exposes exactly a concrete distinguishing context or
universal response equality. For that same-interface admitted quotient,
`contextDecision` projects the universal constructor from admissibility and
`noContextDefect` excludes the other constructor with zero checks; applications
never enumerate outside contexts merely to transport this decision.
If a caller is handling the defect edge propositionally,
`PairCircuit.ContextDefect` retains its one concrete context and response
mismatch, while its generic `impossible` theorem closes the edge against that
same admitted quotient without a second audit.
The following smaller-representative test is also framework-owned:
`PairCircuit.proposal_not_injective` reads the retained distinct identification,
and `smallerRepresentative` projects the `Core.CertifiedReduction` required by
admissibility.  `RepresentativeDecision` therefore carries the available
certificate with zero checks and no candidate-representative universe.

`Core.ResidualRefinement` is the proof-state layer over that occurrence log.
Its `State Residual facts` keeps one stable residual carrier together with a
typed list of every property proved so far.  A `State.Node` receives that
current state, may retrieve any earlier fact, and supplies only its new local
theorem; `Node.run` retains the carrier and prepends the theorem
automatically. `State.StageNode` does the same for data-bearing certificates;
`require` and `requireStage` retrieve inherited facts by type. Existing
decisions are composed with `mapYesStage` and `mapNoStage`, or with
`mapStages` when both existing edges immediately add their next certificate;
`ExactState` kernel-certifies that both branches retain the named carrier. The
`usingFact`/`usingStage` constructors let each consumer name only its immediate
dependency instead of restating the full growing fact schema. Exact chains use
`StageNode.exact`, `mapExactStage`, and `usingFactAndExactStage`, so the actual
retrieved predecessor—not a reconstructed copy—feeds the next stage.
`ResidualRefinement.Ledger` performs the same operation over every actual
occurrence. It starts from a proof-carrying producer, supports tagged branch
append and occurrence restriction, runs theorem or certificate refinements,
and partitions only its literal occurrence schedule with `Ledger.decide`.
The split exposes an equivalence from the disjoint sum of branch occurrences
to the original schedule, hence global unique coverage; it never constructs an
ambient state universe. Complement decisions use `DecisionNode.complement`,
while bounded rank comparisons use `ltOrEqUsingStage`.

`Core.Routing.LedgerExtension Previous Added` is the canonical dependent
extension of a CT-labelled residual stage. Its `previous` field is the literal
complete incoming ledger, and `added` is the one theorem or data value indexed
by that ledger. `ResidualStage.extend` installs the extension without changing
the CT identity. Applications therefore add local mathematics without copying
predecessor fields or rebuilding accumulated state; changing the CT identity
is reserved for an executable `Core.Routing.CTTransition`.

`Graph.ResidualSupportRefinement` packages the graph pattern used by later
support-routing arguments.  An application supplies only a decidable vertex
type and `Event → Finset Vertex`.  The profile derives the exact
occurrence-indexed support view, ordered first-hit/total-absence decision,
linear check ledger, and supported occurrence subtype. Bare schedules use
`viewSchedule`; applications never create an empty-fact state solely for
support projection. Enumerated producers use
`FiniteResidualLedger.Ledger.ofEnumeration` or `ofMappedEnumeration`, then the
same support view. A successful hit
contains the current `ResidualRefinement.State`, so producer origin and every
earlier graph theorem remain available through `FirstHit.get`; recognizing a
support never starts a second provenance proof.

The repository has one explicitly trusted external theorem declaration:
`Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle`. It records
the cited finite `P₁₃`-free minimum-degree-three theorem exactly. The linter,
kernel verifier, and repository tests use an exact path-and-name allowlist;
every other `axiom`, admission, or unsafe declaration remains forbidden.

## Node contract

Every graph node has two simultaneous contracts.

The formal contract is its exact set of incoming and outgoing indexed
`Graph.Edge` constructors. This makes sequencing and predecessor evidence
machine-checkable.

The automation contract classifies:

- proof-instance author inputs;
- typeclass-inferred inputs;
- immediate predecessor inputs;
- other framework-derived inputs;
- generic theorems used;
- states, decisions, certificates, or residuals generated;
- remaining manual obligations.

Every reference is tagged with a `Core.Provision` value. The catalog therefore
supports both a small author-facing view and a complete transitive audit view
without calling both of them “inputs.”

### Typed-transition projection invariant

For each CT, the constructors of its indexed `Graph.Edge` inductive are the
complete authority for intra-CT transitions. The compiled exporter enumerates
those constructors, reduces their source and target indices, records their
exact Lean types, and assigns stable ordinals and IDs. The Cytoscape renderer
must project every catalog transition exactly once, with the same endpoints,
constructor, type, provision, and ordinal. Its visible label is the final
component of the Lean constructor name.

The backend rejects a graph when any transition is missing, duplicated,
renamed, redirected, or changed. The ordinary CT view displays these labels;
expanding one node preserves every surrounding typed transition while adding
the node's internal flow. Executable cross-CT transition profiles remain a
separate overlay and are never counted as intra-CT `Graph.Edge` transitions.

Schema 9 separates this overlay into `transitionFamilies` and
`transitionProfiles`. A family is identified solely by its exact source and
target `Core.CTId` values; its catalog `familyId` is derived as
`sourceTacticId ++ "->" ++ targetTacticId`. A profile is one executable member
of that family. It may specialize the source residual kind, target executable
interface, semantic-discovery mode, selection class, trigger, and result, but
it cannot change the family's source or target CT. Thus the full CT1-to-CT2
profile and its local-deletion profile are distinct executable subtypes of one
CT1-to-CT2 family, not two meanings for the same CT connection.

Each registered-transition example edge selects one `transitionProfileId`.
The canonical registry resolves that profile to exactly one
`advanceExecutor`, and the exporter records that executor as the edge's sole
framework automation owner. A transition constructor is catalog evidence for
the profile's typed kernel; it is never a substitute for execution. Lean
export, catalog hydration, and backend loading reject a missing profile,
source/target disagreement, a constructor-only edge, or any executor other
than the profile's declared `.advance` operation. The framework API reports
the CT catalog and example-catalog verification states independently.

A relationship whose producer is not a CT residual is not a member of this
registry. Graph-level semantic producers describe such a connection with
`Core.SemanticHandoffContract`, which records the source residual kind,
consumer identity, discovery, input constructor, soundness, context
preservation, and provenance. This metadata cannot be promoted to a
`CTTransitionProfileContract`: it has no typed source/target CT family and does
not own mandatory target execution.

## Expandable node internals

Every node also has a Lean-owned `NodeInternalFlowDescriptor`. Its curated
steps are derived from the node automation contract and classify author
objects, inferred instances, predecessor state, framework operations, generic
theorems, and generated outputs. The exporter rejects a descriptor unless it
covers the automation references exactly and every internal edge has valid
endpoints. Capability concepts supply their existing plain-language and
mathematical presentations; other steps retain an exact provisioned reference
and resolve to a compiled declaration whenever one exists.

The catalog exporter reads each resolved declaration from the compiled Lean
environment. It records the exact type, kind, documentation, module, source
range, direct type dependencies, and direct body dependencies, then follows
`StructuralExhaustion.*` dependencies recursively. Lean and Mathlib constants
remain named boundary leaves rather than being expanded into third-party
implementation graphs.

`tools/render_artifacts.py` packages this data as
`generated/internals/CTN.json`, including hashed source text for every
project-local source file. These files are versioned and schema-checked by
`schemas/node-internals.schema.json`. The web backend loads and validates one
file only when `/api/v1/tactics/CTN/internals` is requested. It checks the CT
API version, exact equality with the catalog's node flows and declarations,
dependency closure, safe source paths, hashes, current file contents, and
source ranges before returning the artifact.

The framework explorer therefore keeps its ordinary CT overview unchanged.
After selecting a node, a reader can expand that one node in place, inspect
each step in plain language, formal mathematics where the step denotes a
mathematical concept, and its exact Lean type and source excerpt. Direct
declaration dependencies can then be revealed recursively; project-local
declarations are expandable and external declarations stay collapsed. Only
one high-level node is expanded at a time, and returning to the overview
restores the prior cross-CT transition overlay setting.

## Reference and optimized semantics

The reference implementation uses the declared order of explicit `FinEnum`
values and ordered partial collections. It is executable, exhaustive, and
deterministic. Optimizations are permitted only behind an
`OptimizedSearch`-style equivalence contract that
proves equality with the reference result. Performance code therefore cannot
silently change branch selection or residual provenance.

## Residual-first executable transitions

A CT terminal is either a closure certificate or a semantic residual. A
residual contains the mathematical obstruction and keeps the shared context as
a dependent index; it does not contain a consumer choice.

`Core.Routing.ResidualStage tactic Residual` pairs the canonical residual with
kernel evidence that the stored value is exactly the preceding stage's output.
Every `Core.Routing.CTTransition sourceTactic targetTactic Source target`
consumes this carrier. The type parameters fix the family identity before any
profile identifier or catalog string is considered. Its private kernel owns
semantic discovery, target-context selection, and target-trigger construction;
the `ExecutableInterface targetTactic` owns the public target runner.

Every registered profile exposes one mandatory `.advance` executor. It reads
the exact source stage, performs discovery, constructs the indexed target
input, and executes the target CT. Enabled execution returns an
`EnabledStage` retaining the entire predecessor and the target execution;
disabled discovery retains a proof that no seed exists. Profiles whose seed is
forced use the enabled form internally, but still expose the same full
transition boundary. An application may provide only the profile's declared
target capability, minimality kernel, or semantic-discovery adapter. It cannot
stop after trigger construction, substitute the transition constructor for
`.advance`, or manufacture the target result.

On an enabled branch, the only onward CT input is
`EnabledStage.ledgerStage`. This changes the CT label to the target while
storing the exact predecessor and target execution together. Repeated
transitions therefore build a proof-indexed accumulated ledger automatically.
Within the current CT, `ResidualStage.extend` adds a dependent
`LedgerExtension`; across CTs, the next profile consumes `.ledgerStage`. No
application-defined predecessor equality, copied context, detached trigger,
or alternate residual carrier is permitted.

Applications do not re-expand the internal `onLedger` construction.
`Core.Routing.CTTransition.OutputLedger` is the canonical enabled type for a
registered specialized profile. Ordinary total accumulated edges use
`Routes.Accumulated.OutputLedger` with `advanceCurrent` for the identity
projection without spelling `id`; `ProjectedOutputLedger` and `advance` are
reserved for a genuine mathematical projection. Ordinary
pointwise edges use `PointwiseOutputLedger`/`advancePointwise`; a pointwise
family of selected specialized routes uses
`SelectedPointwiseOutputLedger`/`advanceSelectedPointwise`. These are one API
surface over the same exact-predecessor kernel, not additional edge kinds.

Target entries may themselves vary pointwise over local indices.
`Core.Routing.PointwiseExecutableFamily tactic` packages one already selected
context and trigger for each index, and its `executableInterface` returns the
dependent function of the actual public executions. The index type need not be
finite or enumerable: this construction defines no traversal, search, product
materialization, or ambient-universe scan. It is a specialized target
executable interface inside an ordinary transition profile, not another
transition mechanism.

The semantic-discovery mode is explicit in every profile. Capability discovery
derives the seed from the target capability; a problem semantic adapter
extracts only the mathematically necessary seed from the exact source
residual. CT9-to-CT7, for example, maps the retained capacity-one overload pair
to two comparison objects without rescanning the source collection. The
CT1-to-CT12 adapter proves the declared relation between the successful CT1
theorem and an independent CT12 loop seed; it cannot inspect proof-valued data
to synthesize computation. Context construction, target execution, accumulated
ledger output, and transition provenance remain framework-owned in both modes.

## Verification boundary

Repository verification checks:

- all 17 automation stacks and executable fixtures compile;
- there are no admissions, hidden solvers, caller-authored node
  implementations, or cross-CT producer imports;
- every nonterminal has one automation contract and explicit generated output;
- graph ordinals, endpoints, terminal maps, reachability, and cycles agree with
  the compiled Lean declarations;
- every capability contract contains only author-supplied primitives and names
  its framework-derived operations;
- every generated schema and diagram is a fresh projection of the catalog;
- every displayed CT transition agrees one-to-one with a compiled indexed
  `Graph.Edge` constructor, including its endpoints and exact type;
- every per-CT internal-flow artifact agrees with the compiled catalog and
  current hashed Lean sources;
- every transition profile belongs to the family determined by its exact
  source/target CT identities, resolves to its mandatory `.advance` executor,
  preserves the complete incoming ledger, and declares its semantic-discovery
  authoring mode;
- every non-CT graph-producer handoff has a `SemanticHandoffContract` and is
  absent from the executable transition registry.

## Worked-example manuscript traceability

Worked examples may attach an `ExampleManuscriptDescriptor` to their compiled
`ExampleDescriptor`. A proof step records its stable LaTeX labels and diagram
nodes, plain-language explanation, rendered mathematical statement,
correspondence class, scope limit, local work bound, and declaration groups.
Declaration groups distinguish mathematical definitions and semantic theorems
from encoding bridges, tactic executions, trace/totality audits, complexity
bounds, reusable interfaces, provenance theorems, fixtures, and external
theorems.

`ExampleManuscriptDescriptor.nodeObligations` is the Lean-owned
property-level ledger for audited diagram cells. Each stable task names its
node, status, statement, and evidence proof-step IDs. Export validation rejects
dangling evidence, evidence attached to another node, a proved task backed by
an unfinished step, and any disagreement between a complete node ledger and
`formalizedNodeIds`. The web layer renders this projection; it is not a second
status authority.

For every implemented step, the Lean exporter requires the declaration groups
to cover exactly every declaration displayed by the corresponding stage and
its problem/framework bindings. The example renderer independently verifies
that the manuscript path is repository-relative, every referenced LaTeX label
exists uniquely, every diagram-node number exists, and the compiled source
ranges still match the embedded Lean sources. It parses the complete TeX
document once and emits exactly one normalized fragment for every referenced
label. Theorem-like fragments include the immediately adjacent proof; section
fragments end at the next equal-or-higher heading. Optional environment titles
and the capitalization distinction between `\cref` and `\Cref` are retained.
Unknown Pandoc nodes are fatal rather than silently omitted. TikZ figures
inside a selected fragment
are compiled from the original preamble, converted to SVG, sanitized, and
hashed. The hydrated coverage counts are therefore audit data, not a UI
estimate. Mathematical explanation strings are inspection prose; the compiled
declaration types remain the formal authority.

The Erdős--Gyárfás artifact remains a member of the compiled example catalog,
but its canonical browser URL is `/erdos-gyarfas`. The dedicated page reads
the same immutable `erdos-64` detail artifact and reuses the same synchronized
proof-step, graph, declaration, and Lean-source state. No second mathematical
catalog is introduced. `/examples/erdos-64` redirects to the dedicated reader;
all other `/examples/:exampleId` URLs retain the generic example workspace.
The EG source companion offers `Lean` and `Paper` modes. Paper mode follows the
same active proof-step/declaration state, presents multiple Lean-owned labels
as tabs, and renders only the generated structured fragments. KaTeX runs with
trust disabled and SVG is displayed through an image data URI, so neither raw
TeX nor generated SVG is inserted into the application DOM. Ordinary framework
examples retain their existing Lean-only source viewer.
