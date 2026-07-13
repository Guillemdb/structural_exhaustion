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
target-capability discovery and the shared minimality kernel. CT2-to-CT3 and
CT2-to-CT10 each receive one reusable problem-specific semantic discovery
adapter. Route modules construct the destination trigger and prove
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
ranges still match the embedded Lean sources. The hydrated coverage counts are
therefore audit data, not a UI estimate. Mathematical explanation strings are
inspection prose; the compiled declaration types remain the formal authority.
