# Structural Exhaustion

This repository formalizes the seventeen structural-exhaustion closure tactics
as reusable, automation-first Lean machines. A proof instance supplies only
problem-specific mathematical primitives. The framework performs the finite
searches and verified computations, constructs predecessor-indexed states and
semantic residuals, records typed graph paths, proves tactic-level properties,
and generates the JSON and manuscript views.

The entire Lean implementation is built on Mathlib 4.31.0 and the matching
Lean 4.31.0 toolchain. Framework modules use Mathlib's standard finite,
arithmetic, and graph-theoretic APIs wherever they provide the required
concept; project-defined structures are reserved for CT machine contracts and
deterministic execution semantics that Mathlib does not model.

## External graph-problem examples

Graph applications are independent Lake packages. They depend on Mathlib and
on the framework through `path = "../../lean"`; the framework never imports an
application. This gives the repository live external-consumer checks rather
than in-library demos.

```bash
make mathlib-cache
make framework-build
make example-build
```

- [`examples/even_cycle`](examples/even_cycle) proves that every finite simple
  graph of minimum degree at least three contains an even cycle. The reusable
  `Graph.EndpointParityCycle` profile computes an endpoint-maximal path, runs
  CT6 and CT9, constructs the cycle certificate, and validates it with an
  exact CT1 run. The K4 fixture pins all three tactic traces. See the
  [`example README`](examples/even_cycle/README.md) for its module boundary.
- [`examples/erdos_64_eg`](examples/erdos_64_eg) formalizes the current proof
  slice of Erdős Problem 64. Its public proposition is the exact
  Mathlib `SimpleGraph` statement from Google DeepMind's formal-conjectures
  source, pinned at commit `bcaee6031a085e19432540650e1039b7fd1cea36`.
  The package instantiates the minimum-degree cycle profile with the official
  power-of-two length predicate, implements its CT1/CT2 reductions, and maps
  the manuscript's boundaried-compression interface into generic CT3 with
  verified soundness, typed traces, and totality.
- [`examples/greedy_coloring`](examples/greedy_coloring) completely proves the
  Mathlib-native theorem `G.Colorable (G.maxDegree + 1)`. The graph layer
  generates a bounded elimination order, runs CT12's canonical list-peeling
  machine, uses CT4's functional-cardinality profile at every coloring step,
  constructs the proper coloring, and validates it with an exact CT1 run. Its
  `K₄` fixture pins the computed coloring and all three tactic terminals.
- [`examples/mantel`](examples/mantel) proves Mantel's theorem for Mathlib
  finite simple graphs. The graph layer owns the degree identities,
  Cauchy--Schwarz estimate, CT11 negative-budget localization, and the
  triangle-free contradiction. The external package supplies only the graph
  and its `CliqueFree 3` hypothesis; `K₄` pins the exact CT11 trace and `C₅`
  checks the completed theorem.

## Canonical source and generated views

The only authored CT implementations are under
[`lean/StructuralExhaustion`](lean/StructuralExhaustion). The ordered registry
in
[`Canonical/Registry.lean`](lean/StructuralExhaustion/Canonical/Registry.lean)
binds CT1--CT17, their capability contracts, node automation contracts,
residual kinds, and proved route contracts. The exporter reads the compiled
Lean environment, including the actual `Graph.NodeId`, `Graph.Edge`, and
`Graph.Terminal` constructors.

```text
problem primitives
      -> Spec / Capability
      -> State / Search
      -> Graph / Execution / Theorems / Automation
      -> compiled Lean registry
      -> generated/lean-machines.json
      -> schemas, diagrams, indexes, binding checks, and manuscript figures
```

Do not edit these derived paths by hand:

- `generated/`
- `schemas/generated/`
- `framework/generated/`
- `docs/ct-machines.md`
- `lean/StructuralExhaustion/Generated/BindingCheck.lean`
- `SHA256SUMS`

Use `make generate` to replace the Lean-derived projections. Use `make verify`
to regenerate those projections and refresh `SHA256SUMS`.

## The proof-instance API

Start by defining one shared `Core.Problem`:

```lean
def problem : StructuralExhaustion.Core.Problem where
  Ambient := MyObject
  Baseline := MyBaseline
  rank := myRank
  BranchState := MyBranchState
```

Tactic inputs are indexed by a shared `Core.BranchContext`,
`Core.AvoidingContext`, or `Core.MinimalCounterexampleContext`. This makes the
context components retained by the target agree definitionally across routes.
For example, CT2-to-CT3 and CT2-to-CT10 project a minimal-counterexample context
to its inherited branch context. A producer emits a semantic residual; the
route layer constructs the consumer trigger.

For each CT, define its `Spec`, `Capability`, or primitive system records with
only the data that cannot be derived generically. CT1 follows the same
`Capability` naming convention as the other tactics:

| Tactic | Problem-specific primitives |
|---|---|
| CT1 | Test-index type, dependent witnesses, realization predicate, explicit finite enumerators, and a realization decider. |
| CT2 | Enumerated pieces with properness/admissibility; a piece-to-interface map; enumerated compatible contexts, gluing, reconstruction; baseline/target deciders; deletion; enumerated replacements and strict decrease. |
| CT3 | Pieces, contexts, candidates and table rows; exact responses; admissibility/smaller predicates; explicit context/candidate/row enumerators and their deciders. |
| CT4 | Demands and payers; eligibility, demand weights and capacities; explicit finite enumerators, eligibility decider, and required bound. |
| CT5 | Sites and dependent witnesses; active/support predicates, contributions, finite enumerators, deciders, required amount and capacity. |
| CT6 | Ordered indices, failure predicate/data, contribution, explicit finite failure order, and failure decider. |
| CT7 | Objects and contexts; realization and exact response functions; finite comparison enumerators and realization decider. |
| CT8 | Exact-type and response-context enumerators, exact-type/response operators, and the problem-specific removal operation. |
| CT9 | Item and label types, explicit label enumerator, label map, and capacity. |
| CT10 | Explicit class enumerator, class observation, direct-case predicate, and promotion operator. |
| CT11 | General API: cell type, admissibility predicate/decider and local budget; each invocation supplies its finite cell collection and negative-total proof. For universally admissible decompositions, `NegativeBudgetProfile` reduces the static API to the cell type and local budget. |
| CT12 | Indexed state and peeled-object types, peel operation, and a nonempty restoration operator whose recursive branch carries strict decrease. |
| CT13 | Enumerated payers and obstructions, eligibility, fallback/cost data, ordered tier-two resources, charge and demand, with required deciders. |
| CT14 | Enumerated members, per-member lower mass, optional capacity and label, and label equality. |
| CT15 | Coordinates, target-dependence predicate/decider, charge, and capacity. |
| CT16 | Coordinates and support predicate/decider, closed-code representation/equality, code computation, and target code. |
| CT17 | Target/block/orbit values, compatibility, finite target/offset/position enumerators, finite scale bound, and arithmetic deciders. |

CT2 does not require a finite global interface type. Explicit enumerators are
required for `Piece G`, for the compatible contexts of a selected interface,
and for the legal candidates of a selected piece.

Total search universes are direct Mathlib `FinEnum` values. A capability stores
the value explicitly, so the enumeration order is a visible part of the
machine contract rather than a hidden global instance:

```lean
class FinEnum (α : Type) where
  card : Nat
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]
```

Mathlib derives the exhaustive duplicate-free order with `FinEnum.toList`.
Use `Core.OrderedCollection` only for a partial duplicate-free list whose
first-hit order is observable. Use Mathlib `Finset` for unordered finite sets,
cardinalities, and sums.

A capability may contain a small semantic bridge such as a reconstruction or
refinement theorem. Node decisions, tactic outcomes, certificates, residuals,
graph edges, and downstream inputs are framework outputs. The architecture
linter enforces this boundary, rejects cross-CT producer imports and
whole-result capability fields, and rejects admissions, unsafe declarations,
reverse imports from the framework into applications, and unscoped use of the
`Classical` namespace. Mathlib imports themselves are part of the supported
foundation.

CT1 defines its canonical target as finite realization. An independently named
public target may supply `CT1.TargetBridge`; this optional bridge relates the
public predicate to the canonical target and is not a node or route input.

The framework also provides high-level constructors for recurring instance
shapes:

- `Core.FiniteSaturation.Machine` owns deterministic first-enabled iteration,
  well-founded execution, and the terminal saturation proof.
- `CT1.TargetEncoding` generates a one-test spec, capability, and public-target
  bridge from a finite code checker and encode/decode maps;
  `CT1.runC1OfPublicTarget` packages the exact C1 run.
- `CT2.Capability.deletionOnly` generates unit interfaces, identity contexts,
  and an empty replacement universe; `CT2.DeletionClosureRule` derives the
  deletion witness, closing analysis equality, exact deletion-C2 run,
  contradiction, disabled discovery, and non-properness conclusion from
  baseline preservation and target monotonicity.
- `CT6.ActiveLedgerRun` and `CT9.OverloadedRun` keep the actual execution,
  residual, terminal, and trace aligned. `CT9.parityCapacityOne` additionally
  generates the two-label capacity-one pigeonhole machine from a rank map.
- `CT4.FunctionalCardinalityProfile` generates all irrelevant charging fields,
  the complete CT4 capability, the exact run, and its missing-demand residual
  from functional eligibility and a strict finite-cardinality gap.
- `CT12.ListPeeling` generates indexed states, head/tail decompositions,
  strictly decreasing restoration steps, the exact run, and its exhaustion
  theorem for any list-valued schedule.
- `Graph.MinimumDegreeCycle.StaticInput` generates a Mathlib finite-graph
  problem, cycle target, complete CT1 encoding, deletion-only CT2 capability,
  closure rule, and tight-endpoint theorem from a branch-state family, a
  degree threshold, and a decidable cycle-length predicate.
- `Graph.EndpointParityCycle.Profile` generates the greedy maximal path, CT6
  closure, typed CT6-to-CT9 route, parity overload, path-position
  localization, chord cycle, target theorem, and exact CT1 run. Its
  `Profile.evenCycle` constructor has no theorem-specific proof obligations.
- `Graph.GreedyColoring` generates a certified bounded elimination order and
  deterministic Mathlib coloring. The general
  `colorable_of_bounded_order` theorem supports degeneracy-style applications;
  `colorable_maxDegree_succ` discharges the bound from `FiniteObject.maxDegree`.

For example, the complete even-cycle problem selection is one line:

```lean
abbrev profile (V : Type u) :=
  StructuralExhaustion.Graph.EndpointParityCycle.Profile.evenCycle V
```

The exact authoring surface is machine-readable. After `make export`, inspect
it with:

```bash
jq '.tactics[] | {
  tacticId,
  requiredDefinitions: .capability.requiredDefinitions,
  requiredInstances: .capability.requiredInstances,
  derivedOperations: .capability.derivedOperations,
  capabilityProfiles
}' generated/lean-machines.json
```

Every CT's `Automation.lean` also exports:

- `capabilityContract`, the complete problem-author boundary;
- `nodeAutomationContracts`, one contract per executable graph node;
- `residualKindContracts`, the route-facing semantic residual API;
- execution syntax, soundness syntax, and totality syntax for that tactic.

The canonical public `run` and `ctN_execute` surfaces return the
evidence-carrying `ExecutionResult`: the selected terminal, its typed
`Graph.Path`, and terminal-indexed outcome remain available together. There is
no separate outcome-only public runner.

Each node contract separates author inputs, typeclass-inferred inputs,
predecessor state, framework-derived operations/theorems, generated outputs,
and manual obligations. Every generated output is a typed state, decision,
certificate, residual, or audit object. The intended manual-obligation count is
zero.

Route contracts form a separate authoring boundary. The `semanticDiscovery`
field distinguishes target-capability discovery from a problem semantic
adapter:

| Route | `semanticDiscovery.kind` | Problem-specific route inputs | Adapter |
|---|---|---|---|
| CT1 residual avoidance to CT2 | `capabilityDiscovery` | `targetCapability`, `minimalityKernel` | none |
| CT2 separating context to CT3 | `problemSemanticAdapter` | `targetCapability`, `semanticDiscoveryAdapter` | `PieceDiscovery` |
| CT2 criticality to CT10 | `problemSemanticAdapter` | `targetCapability`, `semanticDiscoveryAdapter` | `DataDiscovery` |
| CT6 active ledger to CT9 | `problemSemanticAdapter` | `targetCapability`, `semanticDiscoveryAdapter` | `ItemCollectionAdapter` |

Capability discovery removes only the residual-specific adapter. For every
route, framework declarations own route-rule construction, target-context and
trigger construction, soundness, context preservation, and provenance.

## Running a tactic in Lean

Use the compiled examples as the canonical invocation templates; tactic
arguments differ because their inputs are dependently typed. For CT1 and CT2:

```lean
def ct1Result := ct1_execute input using ct1Capability

example : CT1.OutcomeClaim ct1Result.outcome := by
  ct1 input using ct1Capability

def ct2Discovery :=
  ct2_discover ct2Capability at minimalContext

def ct2Result (ct2Input : CT2.Input ct2Capability minimalContext) :=
  ct2_execute ct2Capability at minimalContext on ct2Input

example (ct2Input : CT2.Input ct2Capability minimalContext) :
    (ct2Result ct2Input).outcome.Valid := by
  ct2 ct2Capability at minimalContext on ct2Input
```

`ct2Discovery` returns `.enabled ct2Input` or `.disabled reject`. The enabled
branch invokes `ct2Result`; the disabled branch carries
`reject : CT2.Input ct2Capability minimalContext → False`. Discovery is the
canonical pre-step and is not a CT2 graph node; `CT2.run` consumes the
proof-carrying input without repeating piece search.

Compile individual fixtures from `lean/`:

```bash
lake env lean StructuralExhaustion/Examples/CT1AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/CT2AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/CT1ToCT2AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/CT2ToCT3AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/CT2ToCT10AutomationFirst.lean
lake env lean StructuralExhaustion/Examples/FiniteSaturation.lean
lake env lean StructuralExhaustion/Examples/CT2DeletionClosure.lean
lake env lean StructuralExhaustion/Examples/CT6ToCT9AutomationFirst.lean
```

CT3--CT17 have corresponding `CTNAutomationFirst.lean` fixtures. Each fixture
executes concrete branches and kernel-checks the relevant result, trace,
soundness, totality, and determinism statements.

For each registered route, discovery returns an exact seed or a proof that no
seed exists. The framework then constructs the context-indexed trigger and
proves route soundness, context preservation, and provenance.

Inspect the exact route boundary after export with:

```bash
jq '.routes[] | {routeId, authoringBoundary}' generated/lean-machines.json
```

## Build, generate, verify, and test

Prerequisites:

- `make`;
- `elan` and `lake` on `PATH` (the repository pins Lean 4.31.0);
- network access for the first dependency resolution and Mathlib cache fetch;
- Python 3.10 or newer;
- the packages in `requirements.txt` for schema validation and tests;
- `latexmk` and the LaTeX packages used by the manuscript for PDF compilation.

See all public targets:

```bash
make help
```

The complete local verification workflow is:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
make test
```

With `uv`:

```bash
uv run --with-requirements requirements.txt make test
```

On a fresh checkout, fetch Mathlib's precompiled oleans before the first
build. This avoids compiling Mathlib from source independently in each external
Lake package:

```bash
make mathlib-cache
```

The targets have the following contracts:

- `make lint` performs the fast source-architecture audit.
- `make framework-build` compiles the reusable framework package.
- `make even-cycle-example-build`, `make erdos-example-build`, and
  `make greedy-coloring-example-build`, and `make mantel-example-build`
  compile one external application each; `make example-build` compiles all
  four.
- `make build` compiles the framework and all external applications.
- `make export` builds Lean and writes `generated/lean-machines.json` from the
  compiled registry.
- `make schemas` exports Lean and regenerates only the concrete JSON Schema
  family and its index.
- `make generate` exports Lean and regenerates all schemas, Mermaid/Cytoscape
  graphs, manuscript CT fragments, indexes, manifests, and the Lean binding
  check.
- `make validate` validates the current generated tree. It does not first make
  stale artifacts current; use `make verify` for that.
- `make kernel` regenerates artifacts, builds Lean, compiles the generated
  binding check, compares a fresh temporary export byte-for-byte, checks the
  pinned toolchain, and rejects authored admissions.
- `make verify` runs the linter, full generation, kernel verification,
  repository/schema/route validation, and checksum refresh.
- `make test` runs `make verify` followed by the Python regression suite.
- `make manuscript` regenerates the CT fragments and compiles
  `build/framework/branch_closure_methodology_extended.pdf`.

Useful direct commands are:

```bash
make build
python3 tools/lint_automation_first.py --root .
python3 tools/render_schemas.py --catalog generated/lean-machines.json --root .
python3 tools/validate_repository.py --root .
python3 tools/verify_lean.py
python3 tools/validate_machine_run.py path/to/run.json
```

To inspect the current compiled inventory without relying on hard-coded counts:

```bash
jq '{
  tactics: (.tactics | length),
  nodes: ([.tactics[].nodes[]] | length),
  typedEdges: ([.tactics[].transitions[]] | length),
  terminals: ([.tactics[].terminals[]] | length),
  residualKinds: ([.tactics[].residualKinds[]] | length),
  routes: (.routes | length)
}' generated/lean-machines.json
```

## Repository layout

- `lean/StructuralExhaustion/Core/`: shared problems, contexts, finite search,
  routing, provenance, and smaller-object theorems.
- `lean/StructuralExhaustion/Graph/`: reusable Mathlib-based graph adapters and
  CT profiles shared by graph-combinatorial applications.
- `lean/StructuralExhaustion/CT1/` through `CT17/`: canonical tactic modules.
- `lean/StructuralExhaustion/Routes/`: typed residual-first route rules.
- `lean/StructuralExhaustion/Examples/`: framework-owned kernel fixtures for
  the generic CT APIs.
- `lean/StructuralExhaustion/Canonical/`: registry and compiled-environment
  exporter.
- `examples/even_cycle/`: independent Lake package containing the complete
  worked theorem instantiation and executable end-to-end fixture.
- `examples/erdos_64_eg/`: independent Lake package containing the official
  Erdős 64 boundary, the current CT1/CT2 instantiation, and the next CT3 author
  contract.
- `examples/greedy_coloring/`: independent Lake package containing the complete
  CT12/CT4/CT1 greedy-coloring theorem and executable `K₄` fixture.
- `examples/mantel/`: independent Lake package containing the complete
  CT11-based Mantel theorem, an executable localization fixture, and a
  triangle-free `C₅` theorem check.
- `schemas/`: authored generic schemas and Lean-derived concrete schemas.
- `generated/`: catalog, graph projections, manifests, summaries, and indexes.
- `framework/`: the manuscript and generated CT fragments.
- `tools/`: generic export rendering, validation, linting, and verification.
- `tests/`: repository architecture and regression tests.

See [`lean/README.md`](lean/README.md) for node-level maintenance guidance and
[`schemas/README.md`](schemas/README.md) for the JSON authority boundary.
