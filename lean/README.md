# Automation-first Lean CT library

This directory contains the only authored implementation of CT1–CT17. The
public API consists of primitive capability records, evidence-carrying reference
runners, verified theorem surfaces, semantic residuals, and executable typed transitions.

Worked theorem instantiations are not part of this package. The even-cycle and
partial Erdős Problem 64 applications live in
[`../examples/even_cycle`](../examples/even_cycle) and
[`../examples/erdos_64_eg`](../examples/erdos_64_eg) as independent Lake
packages with this directory as a path dependency. Files under
`StructuralExhaustion/Examples` are framework API fixtures, not theorem-domain
implementations.

The package depends on Mathlib 4.31.0. Core and graph-support modules use
Mathlib definitions and theorems wherever possible; framework-owned types
represent only CT contracts, typed machine state, provenance, and exact
deterministic execution policy.

## Proof-instance boundary

A problem instantiation supplies only mathematical primitives that the generic
framework cannot derive:

- the ambient `Core.Problem` and shared branch context;
- CT-specific types and primitive predicates or operators;
- explicit Mathlib `FinEnum` values fixing exhaustive reference order;
- decision procedures for primitive predicates;
- the small number of semantic bridge theorems that are not definitional.

The framework owns finite search, exhaustive decisions, first-hit policy,
state construction, certificates, residuals, graph edges, typed traces,
soundness, totality, determinism, and executable CT-transition construction. A capability
field contains primitive semantics or a strictly local bridge; complete tactic
outcomes, final theorems, and downstream tactic inputs are framework outputs.

Capabilities store explicit `FinEnum` values because enumeration order is part
of the reference machine's deterministic semantics. Mathlib derives an
exhaustive duplicate-free list from each value. `Core.OrderedCollection` is
reserved for partial ordered frontiers; order-insensitive finite reasoning uses
Mathlib `Finset`.

## Mathlib graph support

`StructuralExhaustion.Graph` uses Mathlib `SimpleGraph`, `Walk`, `Path`,
`Dart`, degree, minimum degree, edge finsets, and graph inclusion directly.
`Graph.FiniteObject` adds only the explicit `FinEnum` schedule and adjacency
decider needed by deterministic runners.

Reusable profiles remove graph-problem boilerplate:

- `Graph.MinimumDegreeCycle.StaticInput` generates the shared problem, target,
  CT1 encoding, deletion-only CT2 machine, closure proof, and endpoint
  criticality theorem.
- `Graph.PackedMinimumDegreeCycle` selects finite graphs by lexicographic
  vertex/edge rank and executes CT2 on one explicit proper-subgraph
  certificate, with cycle transport, typed trace, totality, and a constant
  work bound supplied by the framework. Its composed prefix retains those
  outputs and adds CT3 boundaried replacement/uncompressibility on the same
  selected graph. It can then retain an induced-path CT1 stage on that same
  packed branch. The concrete piece stores an actual packed Mathlib graph and
  injective finite boundary labelling; boundary degrees are computed directly
  from that graph.
- `Graph.InducedPath.Profile` takes a Mathlib induced graph embedding as its
  proof-carrying CT1 code. It provides exact positive and avoiding traces,
  semantic reflection, totality, and constant work bounds without tuple or
  subgraph enumeration.
- `Core.FiniteDisjointPacking` and `CT12.DisjointPacking` select a maximum
  family of pairwise-disjoint nonempty supports at proof level, derive
  maximal saturation, and run CT12 exactly once per selected item with a
  host-vertex bound. `Graph.InducedPathPacking` adds exact support/remainder
  cardinalities and hereditary induced-path-freeness.
- `CT10.ExhaustiveClassification` constructs an exact accepted-subtype table
  from an explicit finite candidate universe and proves the exhaustive
  terminal, trace, validity, totality, and quadratic work bound.
  `Graph.InducedPathAttachment` adds compact label codes, symbolic no-gap
  semantics, `C`/`omegaTwo`, and literal attachment-cycle certificates.
- `Graph.FiniteObject.InternalSubgraph` packages arbitrary finite subgraphs on
  explicit supports and proves that passing to the induced graph on the same
  support cannot lower minimum degree.
- `Graph.EndpointParityCycle.Profile` generates the maximal-path CT6 run,
  typed CT6-to-CT9 transition, parity CT9 run, chord-cycle theorem, target proof,
  and final CT1 validation.
- `Graph.GreedyColoring` derives the bounded order, CT12 peeling audit,
  CT4 coloring steps, Mathlib coloring certificate, and CT1 validation.
- `Graph.Mantel` derives the degree identities, CT11 negative-budget
  localization, and triangle-free endpoint-degree contradiction used in
  Mantel's theorem.

The generic CT3 layer accepts application-defined pieces, contexts,
candidates, rows, finite enumerations, and primitive deciders through
`CT3.Spec` and `CT3.Capability`. `Graph.PackedBoundariedGluing` is the
airtight graph replacement profile: it owns literal gluing, exact size and
degree transport, locally derived whole-graph decrease, target transport,
the typed compression run, totality, and constant budget. Applications supply
only their target predicate, threshold, and local replacement data. The external even-cycle, Erdős 64,
greedy-coloring, and Mantel packages are living consumers of these interfaces,
and graph-support modules remain application-independent.

`Graph.External.HegdeSandeepShashank` contains the sole trusted external
theorem declaration used by the Erdős example. Its exact path and declaration
name are allowlisted by repository tooling; all other axioms, admissions, and
unsafe declarations are rejected.

## Canonical tactic layers

Every CT exposes the following dependency direction:

```text
Spec / primitive systems
        ↓
Capability (minimal proof-instance API)
        ↓
State (predecessor-indexed evidence)
        ↓
Search (reference algorithms)
        ↓
Graph (evidence-carrying edges and typed paths)
        ↓
Execution → Theorems → Automation
```

Some tactics split a large primitive system or a large node implementation
across additional files. Those files do not change the direction above.

Each `Automation.lean` exports:

- `capabilityContract`: the exact proof-author surface and the operations
  derived by the framework;
- `nodeAutomationContracts`: execution class, author inputs, inferred and
  predecessor dependencies, generic theorems, generated outputs, and remaining
  manual obligations for every executable node;
- `residualKindContracts`: semantic residual fields and inherited context;
- `ctN_execute`, `ctN`, and `ctN_total` syntax.

The indexed `Graph.Edge` constructors are the node-to-node API. A successor can
receive only the exact state proved by its predecessor. `ExecutionResult`
contains a path indexed by the actual terminal, and the public theorem surface
proves soundness, totality, deterministic reference semantics, trace validity,
and outcome exhaustiveness.

## Executable CT transitions

Catalog schema 9 separates cross-CT execution into `transitionFamilies` and
`transitionProfiles`. A family is fixed by the exact source and target
`Core.CTId` values. A profile is one executable member of that family and may
specialize the source residual, target executable interface, selection class,
and semantic-discovery boundary without changing either CT identity. The
modules under `StructuralExhaustion/Routes` implement these profiles; the
namespace is organizational and does not define a second transport API.

Every profile consumes a `Core.Routing.ResidualStage sourceTactic Ledger`,
where `Ledger` is the complete accumulated residual. Its public `.advance`
operation performs semantic discovery, constructs the target input, executes
the target CT's public interface, retains the exact predecessor, and records
transition provenance. Applications must invoke `.advance` and may continue
only through the enabled stage's `.ledgerStage`. A bare target result, local
residual wrapper, or separately constructed target input cannot become the
next CT stage.

`Core.Routing.PointwiseExecutableFamily` handles a public CT execution at each
local index. Its executable interface returns the dependent function of those
pointwise executions; it performs no enumeration and requires no `FinEnum`,
list, scan, or synthesized index universe.

A graph-level producer that is not a CT residual uses
`Core.SemanticHandoffContract`. That record documents the source residual,
consumer, semantic discovery, input constructor, soundness, context
preservation, and provenance, but it is not executable and cannot appear in
the CT-transition registry. Producers never import consumers.

## Work on one node

When adding or strengthening a node:

1. Add only primitive problem data to `Spec` or `Capability`.
2. Put every derivable search or case split in `Search`.
3. Represent the result as a predecessor-indexed state, decision, certificate,
   or residual.
4. Carry that result through one indexed graph edge.
5. Add its `NodeAutomationContract`, including explicit generated outputs and
   an empty `manualObligations` list whenever the framework can discharge all
   proof work.
6. Prove the local search theorem, then reuse it in aggregate soundness and
   totality.
7. Add a concrete fixture covering each outcome and malformed-presentation
   tests where relevant.
8. Run the architecture linter and Lean build from the repository root.

## Direct commands

```bash
cd lean
lake exe cache get
lake build
lake env lean StructuralExhaustion/Examples/CT1AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/CT2AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/CT1ToCT2AutomationFirst.lean
```

Repository-wide export, schema generation, validation, and manuscript
compilation are exposed by the root `Makefile`.
