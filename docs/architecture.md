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
 semantic residual + declared semantic discovery
                     ↓
             typed RouteRule ── target trigger
                     ↓
       compiled-environment catalog exporter
                     ↓
 schemas, diagrams, audit reports, and manuscript figures
```

No generated layer may declare a node, edge, capability field, residual, or
route that is absent from Lean.

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

The repository linter rejects the legacy API vocabulary, cross-CT imports in a
producer, admissions, nonconstructive dependencies, suspicious whole-result
capability fields, and obsolete compatibility files.

## Mathlib graph specialization

`Graph.FiniteObject` is the graph layer's mathematical object: a Mathlib
`SimpleGraph` paired with the explicit execution order and adjacency decision
procedure required by deterministic search.
`MinimumDegreeCycle.StaticInput` generates CT1 and CT2 from the
minimum-degree/cycle contract. `MinimumDegreeCycleRouted` generates the
edge-rooted CT1 encoding, certificate-to-local-deletion route composition,
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
CT6-to-CT9, CT9, chord-cycle, and CT1-validation pipeline on top. External
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
the node's internal flow. Registered residual-to-CT routes remain a separate,
explicit overlay and are never counted as intra-CT `Graph.Edge` transitions.

The main framework graph also projects every direct CT-to-CT relationship in
the compiled example workflows. These edges are example-backed implemented
transitions, not additional `Core.Routing.RouteRule` instances. Each keeps its
original relationship kind, example and workflow identity, endpoint stages,
primary declarations, and evidence declarations. Consequently a theorem
composition such as the Erdős CT10-to-CT6 step is visible without being
misclassified as a reusable registered residual route. The framework API
reports the CT catalog and example-catalog verification states independently.

Every such direct cross-CT edge must also name at least one compiled,
framework-owned automation declaration. Registered routes name their reusable
`routeContract`; ordinary compositions name the Core, CT, Route, or Graph
executor that constructs or certifies the transition. Lean export, catalog
hydration, and backend loading all reject missing, example-local, or
`Graph.External` automation. The main framework graph and example inspector
show these automation declarations separately from theorem-specific evidence.

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
restores the prior cross-CT route setting.

## Reference and optimized semantics

The reference implementation uses the declared order of explicit `FinEnum`
values and ordered partial collections. It is executable, exhaustive, and
deterministic. Optimizations are permitted only behind an
`OptimizedSearch`-style equivalence contract that
proves equality with the reference result. Performance code therefore cannot
silently change branch selection or residual provenance.

## Residual-first routing

A CT terminal is either a closure certificate or a semantic residual. A
residual contains the mathematical obstruction and keeps the shared context as
a dependent index; it does not contain a consumer choice.

`Core.Routing.RouteRule` separately declares capability discovery, target
context, trigger construction, and stable route identity. Enabled discovery
produces a well-typed trigger. Disabled discovery retains a proof that no seed
exists. Each route contract records its authoring boundary. CT1-to-CT2 uses
target-capability discovery and the shared minimality kernel. CT1-C1-to-CT12,
CT2-to-CT3, CT2-to-CT10, CT6-to-CT9, and CT9-to-CT7 each receive one reusable
problem-specific semantic adapter. The CT9-to-CT7 adapter maps the exact
capacity-one overload pair to the consumer's two comparison objects without
rescanning the source collection. For CT1-to-CT12 the adapter must prove the
declared relation between the successful CT1 theorem and the independent CT12
loop seed; it cannot inspect the proof-valued source to generate computation.
Route modules construct the destination trigger and prove
branch-context preservation, soundness, and provenance once.

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
- every registered route has discovery, trigger, soundness, context
  preservation, provenance, and an explicit semantic-discovery authoring mode.

## Worked-example manuscript traceability

Worked examples may attach an `ExampleManuscriptDescriptor` to their compiled
`ExampleDescriptor`. A proof step records its stable LaTeX labels and diagram
nodes, plain-language explanation, rendered mathematical statement,
correspondence class, scope limit, local work bound, and declaration groups.
Declaration groups distinguish mathematical definitions and semantic theorems
from encoding bridges, tactic executions, trace/totality audits, complexity
bounds, reusable interfaces, provenance theorems, fixtures, and external
theorems.

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
but its canonical browser route is `/erdos-gyarfas`. The dedicated page reads
the same immutable `erdos-64` detail artifact and reuses the same synchronized
proof-step, graph, declaration, and Lean-source state. No second mathematical
catalog is introduced. `/examples/erdos-64` redirects to the dedicated reader;
all other `/examples/:exampleId` routes retain the generic example workspace.
The EG source companion offers `Lean` and `Paper` modes. Paper mode follows the
same active proof-step/declaration state, presents multiple Lean-owned labels
as tabs, and renders only the generated structured fragments. KaTeX runs with
trust disabled and SVG is displayed through an image data URI, so neither raw
TeX nor generated SVG is inserted into the application DOM. Ordinary framework
examples retain their existing Lean-only source viewer.
