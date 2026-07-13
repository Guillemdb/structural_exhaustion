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
minimum-degree/cycle contract. The generic CT3 layer receives
application-defined pieces, contexts, candidates, table rows, finite
enumerations, and decision procedures through its ordinary specification and
capability interfaces. `EndpointParityCycle.Profile` builds the reusable maximal-path, CT6,
CT6-to-CT9, CT9, chord-cycle, and CT1-validation pipeline on top. External
applications select these profiles and retain only their genuinely
theorem-specific predicates and fixtures.

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
