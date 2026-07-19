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
  power-of-two length predicate and reuses the graph layer's edge-rooted CT1,
  lexicographic proper-subgraph CT2 profile, rank-minimal CT1-to-local-CT2
  transition profile, no-proper-core theorem, deletion-criticality theorem,
  and verified CT3 boundaried-replacement/uncompressibility prefix. Its next CT1 stage
  spans manuscript nodes `[15]`--`[16]`: literal induced-`P₁₃`-freeness is
  closed by the isolated Hegde--Sandeep--Shashank external theorem, and the
  forced induced embedding is retained through an exact C1 execution.
  The later verified slice includes the graph-owned ordered surplus CT6 stage
  and its registered CT6-to-CT9 surplus-slot transition, followed by exact
  four-cycle/high-neighbourhood structure, open/triangular selected-port
  classification, centre-fibre CT9, an overload-only CT9-to-CT7 response
  transition, the exact CT5 shoulder ledger, and the framework-owned
  conditional fan-compatibility interpretation, followed by the all-incident-port CT10
  high-centre dichotomy and the CT5 triangular-shoulder completion ledger. The
  current endpoint is `exists_verifiedTriangularShoulderCompletionPrefix`;
  none of these stages enumerates
  port pairs, vertex subsets, completion graphs, or response tables.
  Its generated web descriptor carries the corresponding manuscript roadmap:
  every displayed declaration is assigned to an
  explained mathematical, execution, complexity, provenance, interface,
  fixture, or external-theorem group, with validated LaTeX labels and diagram
  nodes and an explicit remaining node `[19]`--`[20]` frontier.
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
residual kinds, and executable transition profiles. The exporter reads the compiled
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
context components retained by the target agree definitionally across
transitions. For example, CT2-to-CT3 and CT2-to-CT10 project a
minimal-counterexample context to its inherited branch context, while
CT9-to-CT7 maps the exact
capacity-one overload pair to two comparison objects without rescanning the
source fibre. A producer emits a semantic residual in an exact CT-labelled
stage; the selected executable profile consumes that complete stage and runs
the target CT.

For each CT, define its `Spec`, `Capability`, or primitive system records with
only the data that cannot be derived generically. CT1 follows the same
`Capability` naming convention as the other tactics:

| Tactic | Problem-specific primitives |
|---|---|
| CT1 | Test-index type, dependent witnesses, realization predicate, explicit finite enumerators, and a realization decider. |
| CT2 | Full replacement profile: enumerated pieces, contexts, and replacements with their local operators and deciders. Local profiles: either one finite piece schedule and deletion closure, or one explicitly certified smaller object with its reduced baseline and target transport. |
| CT3 | Finite-table profile: pieces, contexts, candidates, rows, exact responses, enumerators, and deciders. Boundaried-replacement profile: one finite boundary-label set, gluing semantics, boundary degrees, one proper atom, and one proof-specified replacement certificate. |
| CT4 | Demands and payers; eligibility, demand weights and capacities; explicit finite enumerators, eligibility decider, and required bound. |
| CT5 | Sites and dependent witnesses; active/support predicates, contributions, finite enumerators, deciders, required amount and capacity. |
| CT6 | Ordered indices, failure predicate/data, contribution, explicit finite failure order, and failure decider. |
| CT7 | Objects and contexts; realization and exact response functions; finite comparison enumerators and realization decider. |
| CT8 | Exact-type and response-context enumerators, exact-type/response operators, and the problem-specific removal operation. |
| CT9 | Item and label types, explicit label enumerator, label map, and capacity. |
| CT10 | General API: explicit class enumerator, class observation, direct-case predicate, and promotion operator. Exact-classification profile: an explicit candidate enumerator plus one decidable acceptance predicate. |
| CT11 | General API: cell type, admissibility predicate/decider and local budget; each invocation supplies its finite cell collection and negative-total proof. For universally admissible decompositions, `NegativeBudgetProfile` reduces the static API to the cell type and local budget. |
| CT12 | General API: indexed state and peeled-object types, peel operation, and a nonempty restoration operator whose recursive branch carries strict decrease. Disjoint-packing profile: finite items, finite nonempty supports, and one representative host vertex per support. |
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
public predicate to the canonical target and is not a node or transition input.

The framework also provides high-level constructors for recurring instance
shapes:

- `Core.FiniteSaturation.Machine` owns deterministic first-enabled iteration,
  well-founded execution, and the terminal saturation proof.
- `CT1.TargetEncoding` generates a one-test spec, capability, and public-target
  bridge from a finite code checker and encode/decode maps;
  `CT1.runC1OfPublicTarget` packages the exact C1 run.
- `Graph.InducedPath.Profile` uses a Mathlib induced graph embedding as a
  proof-carrying CT1 code. It supplies positive and avoiding executions,
  semantic reflection, exact traces, totality, and degree-zero work bounds
  without enumerating vertex tuples or subgraphs.
- `CT2.Capability.deletionOnly` generates unit interfaces, identity contexts,
  and an empty replacement universe; `CT2.DeletionClosureRule` derives the
  deletion witness, closing analysis equality, exact deletion-C2 run,
  contradiction, disabled discovery, and non-properness conclusion from
  baseline preservation and target monotonicity.
- `CT2.CertifiedReductionInput` accepts one proof-specified smaller object,
  its inherited baseline, and target monotonicity. The framework generates the
  canonical deletion-C2 terminal, typed trace, contradiction, totality proof,
  and constant degree-zero work certificate without enumerating pieces or
  ambient objects.
- `Graph.PackedBoundariedGluing` formalizes finite boundary labels, literal
  graph gluing, obstruction profiles, boundary-degree fibres, exact rank and
  degree transport, and universal context response. Its verified stage invokes
  `CT3.runCertifiedCompression` only after deriving the genuine smaller
  counterexample, with a one-check degree-zero budget.
- `CT6.ActiveLedgerRun` and `CT9.OverloadedRun` keep the actual execution,
  residual, terminal, and trace aligned. `CT9.parityCapacityOne` additionally
  generates the two-label capacity-one pigeonhole machine from a rank map.
- `CT4.FunctionalCardinalityProfile` generates all irrelevant charging fields,
  the complete CT4 capability, the exact run, and its missing-demand residual
  from functional eligibility and a strict finite-cardinality gap.
- `CT12.ListPeeling` generates indexed states, head/tail decompositions,
  strictly decreasing restoration steps, the exact run, and its exhaustion
  theorem for any list-valued schedule.
- `Core.FiniteDisjointPacking` proof-selects a maximum family of pairwise
  disjoint nonempty supports and proves maximal saturation without executable
  powerset enumeration. `CT12.DisjointPacking` audits exactly the selected
  list, proves one iteration per selected item, and gives iteration and trace
  bounds linear in the host vertex count.
- `Graph.InducedPathPacking` instantiates that profile with literal Mathlib
  induced embeddings. It supplies exact packed/remainder cardinalities and an
  induced-path-free remainder. `Graph.MaximumMatching` specializes it to
  induced paths of order two and owns the maximum-matching partition,
  selected-list CT12 audit, and edgeless unmatched remainder; the even-cycle
  package is only an external fixture for that API.
- `CT10.ExhaustiveClassification` turns a finite accepted-candidate predicate
  into the exact class table, exhaustive execution, typed trace, totality,
  and a quadratic candidate/class work ledger. `Graph.InducedPathAttachment`
  supplies compact label codes, symbolic gap semantics, compatibility
  relations, and actual attachment-cycle certificates; the Erdős `P₁₃`
  table and Mantel edge table share these APIs.
- `Graph.FiniteObject.InternalSubgraph` represents an arbitrary finite graph
  supported inside a finite host. Its generic minimum-degree monotonicity
  theorem upgrades induced-core exclusions to ordinary-subgraph exclusions.
- `Graph.MinimumDegreeCycle.StaticInput` generates a Mathlib finite-graph
  problem, cycle target, complete CT1 encoding, deletion-only CT2 capability,
  closure rule, and tight-endpoint theorem from a branch-state family, a
  degree threshold, and a decidable cycle-length predicate.
- `Graph.MinimumDegreeCycleRouted` adds the reusable edge-rooted CT1 target,
  proof-carrying positive and avoiding runs, certificate-to-local-deletion
  transition execution, rank-minimal prefix selection, tight-endpoint
  criticality, and high-degree independence.  Both the Erdős and even-cycle
  packages instantiate these declarations.
- `Graph.PackedMinimumDegreeCycle` hides each finite graph's vertex type,
  encodes lexicographic `(vertices, edges)` order as a natural-number rank,
  transports cycles through injective Mathlib graph homomorphisms, and runs
  certificate-driven CT2 on one proper subgraph. Its combined output retains
  the existing edge-rooted CT1 and local-deletion CT2 prefix on the selected
  graph, extends it with the verified CT3 boundaried-replacement stage, and
  can retain a subsequent induced-path CT1 stage on the same packed context.
- `Graph.EndpointParityCycle.Profile` generates the greedy maximal path, CT6
  closure, typed CT6-to-CT9 transition, parity overload, path-position
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
- `residualKindContracts`, the transition-facing semantic residual API;
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

Catalog schema 9 exposes executable cross-CT structure through
`transitionFamilies` and `transitionProfiles`. A family has one exact typed
source/target CT pair. Profiles within that family may specialize the source
residual, target executable interface, selection class, and semantic-discovery
boundary without redefining the CT pair. The `semanticDiscovery` field
distinguishes target-capability discovery from a problem semantic adapter:

| Transition profile | `semanticDiscovery.kind` | Problem-specific inputs | Adapter |
|---|---|---|---|
| CT1 residual avoidance to CT2 | `capabilityDiscovery` | `targetCapability`, `minimalityKernel` | none |
| CT2 separating context to CT3 | `problemSemanticAdapter` | `targetCapability`, `semanticDiscoveryAdapter` | `PieceDiscovery` |
| CT2 criticality to CT10 | `problemSemanticAdapter` | `targetCapability`, `semanticDiscoveryAdapter` | `DataDiscovery` |
| CT6 active ledger to CT9 | `problemSemanticAdapter` | `targetCapability`, `semanticDiscoveryAdapter` | `ItemCollectionAdapter` |

Capability discovery removes only the residual-specific adapter. Every
profile is a typed `Core.Routing.CTTransition` that consumes a
`ResidualStage sourceTactic Ledger`, where `Ledger` is the complete accumulated
residual rather than a freshly wrapped local result. The profile's public
`.advance` is mandatory: it owns exact source lookup, semantic discovery,
target-input construction, public target execution, provenance, and the next
accumulated ledger. Applications continue only through the enabled stage's
`.ledgerStage`; a bare target result is never a successor input.

When a manuscript requires one public CT execution at every local centre,
port, or other index, `Core.Routing.PointwiseExecutableFamily` packages those
pointwise entries as one executable interface. Its result is a dependent
function, not an enumeration: the index type needs no `FinEnum`, list, scan, or
synthesized universe.

Non-CT graph producers are deliberately outside `transitionFamilies` and
`transitionProfiles`. They use `Core.SemanticHandoffContract` to record their
source residual, consumer, semantic discovery, input constructor, soundness,
context preservation, and provenance. Such a handoff cannot enter the
executable CT-transition registry because it does not own a typed CT family or
mandatory target execution.

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

For each registered transition profile, `.advance` returns either an exact
seed-impossibility proof or an enabled target execution retaining the complete
incoming ledger. Only the enabled stage's `.ledgerStage` may feed another CT.

Inspect the exact executable transition boundary after export with:

```bash
jq '.transitionFamilies[] | {familyId, sourceTacticId, targetTacticId, profileIds}' generated/lean-machines.json
jq '.transitionProfiles[] | {profileId, familyId, advanceExecutor, authoringBoundary}' generated/lean-machines.json
```

## Interactive framework explorer

The read-only FastAPI and React application visualizes all seventeen compiled
CT machines, their typed edges, automation contracts, residuals, terminals,
and registered cross-CT transition profiles. Its Examples section also exposes
the four external graph applications, their accurately typed proof-composition flows,
problem/framework interfaces, kernel evidence, and focused or full Lean
source. Erdős 64 remains in that catalog but opens in a dedicated
`/erdos-gyarfas` proof workspace, where the manuscript roadmap, CT flow,
mathematical explanation, and Lean sources can evolve independently of the
generic example reader. Its right-hand companion switches between focused or
full Lean source and label-addressed paper fragments. The paper view renders
the labeled mathematical environment together with its adjacent proof, uses
tabs when one proof step cites several labels, and includes checked SVG output
for selected TikZ figures. It is explicitly marked as a partial proof slice,
and non-CT semantic handoffs remain visibly distinct from executable
transition profiles.

Both sections consume only immutable files under `generated/`. Example
descriptors are exported from each compiled external Lake package; source text
is copied from the exporter-selected modules with declaration ranges and
SHA-256 hashes. The Lean-owned manuscript descriptor selects the TeX labels;
generation parses those labels into a safe document AST, hashes the source and
every fragment, and rejects content it cannot render faithfully. The web layer
does not discover source paths or maintain a second mathematical catalog.

Start the explorer from a fresh checkout with one command:

```bash
make web
```

The first run resolves the pinned npm lockfile and the Python requirements,
builds the React application, and serves the API and browser application
together at `http://127.0.0.1:8000`. This command requires `uv`, Node.js 20.19
or newer, and npm. Override the bind address or port with:

```bash
make web WEB_HOST=0.0.0.0 WEB_PORT=8080
```

`make web` uses the currently committed generated artifacts; it does not
compile Lean. The header reports framework and example freshness independently
whenever either catalog hash differs from `generated/kernel-verification.json`.
For local browsing only, freshness-only hash mismatches produce a terminal
warning and a visible page banner while the explorer continues with the last
generated embedded content. Malformed structure, unsafe paths or SVG, and
missing artifacts still stop startup. Strict export, validation, and test
commands continue to reject stale hashes. Use `make verify` when the generated
projections need to be refreshed.

Run the focused backend and frontend checks with `make web-test`.

## Build, generate, verify, and test

Prerequisites:

- `make`;
- `elan` and `lake` on `PATH` (the repository pins Lean 4.31.0);
- network access for the first dependency resolution and Mathlib cache fetch;
- Python 3.10 or newer;
- the packages in `requirements.txt` for schema validation and tests;
- Pandoc with AST API 1.23.1 for label-addressed paper fragments; and
- `latexmk`, `dvisvgm`, and the LaTeX packages used by the manuscripts for PDF
  and checked SVG figure compilation.

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
- `make export` builds Lean, writes `generated/lean-machines.json` from the
  compiled registry, and regenerates the checked example source and manuscript
  projections.
- `make schemas` exports Lean and regenerates only the concrete JSON Schema
  family and its index.
- `make generate` exports Lean and regenerates all schemas, Mermaid/Cytoscape
  graphs, lazy per-CT node-internal dependency/source artifacts, example
  catalogs and source projections, manuscript CT fragments, indexes,
  manifests, and the Lean binding check.
- `make validate` validates the current generated tree. It does not first make
  stale artifacts current; use `make verify` for that.
- `make kernel` regenerates artifacts, builds Lean, compiles the generated
  binding check, compares a fresh temporary export byte-for-byte, checks the
  pinned toolchain, and rejects authored admissions.
- `make verify` runs the linter, full generation, kernel verification,
  repository/schema/transition validation, and checksum refresh.
- `make test` runs `make verify`, the Python regression suite, and the web
  frontend tests, type-check, and production build.
- `make web` builds and serves the generated-artifact framework explorer.
- `make web-test` runs the focused web API and frontend checks.
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
  transitionFamilies: (.transitionFamilies | length),
  transitionProfiles: (.transitionProfiles | length)
}' generated/lean-machines.json
```

## Repository layout

- `lean/StructuralExhaustion/Core/`: shared problems, contexts, finite search,
  executable transitions, provenance, and smaller-object theorems.
- `lean/StructuralExhaustion/Graph/`: reusable Mathlib-based graph adapters and
  CT profiles shared by graph-combinatorial applications.
- `lean/StructuralExhaustion/CT1/` through `CT17/`: canonical tactic modules.
- `lean/StructuralExhaustion/Routes/`: reusable executable CT-transition
  profiles.
- `lean/StructuralExhaustion/Examples/`: framework-owned kernel fixtures for
  the generic CT APIs.
- `lean/StructuralExhaustion/Canonical/`: registry and compiled-environment
  exporter.
- `examples/even_cycle/`: independent Lake package containing the complete
  worked theorem instantiation and executable end-to-end fixture.
- `examples/erdos_64_eg/`: independent Lake package containing the official
  Erdős 64 boundary and its current theorem-specific CT1/CT2 instantiation.
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
