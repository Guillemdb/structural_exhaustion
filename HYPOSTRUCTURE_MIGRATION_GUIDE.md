# Hypostructure Migration Guide

Status: implementation plan for a clean, incremental rewrite. This document is
the operational companion to:

- `DOMAIN_INDEPENDENT_CORE.md`;
- `GRAPH_LAYER_API.md`; and
- `PDE_LAYER_API.md`.

The new framework is named **Hypostructure**. Its Lean package, library, and
root namespace are all `hypostructure`/`Hypostructure`. The migration is a
translation into a new implementation, not an in-place refactor of
`StructuralExhaustion`.

## 1. End state

At the end of the migration, the repository has:

1. an independent `hypostructure/` Lake package containing the domain-neutral
   Core, CT1-CT17, framework-owned routes, canonical metadata, Graph, and PDE
   layers;
2. a Hypostructure-native Erdos--Gyarfas Problem 64 application whose nodes
   consume only their literal predecessor residual and accumulated framework
   ledger;
3. a Hypostructure-native PDE example package containing small axiom-free
   fixtures and a faithful registration of a two-dimensional Navier--Stokes
   problem;
4. graph and PDE specializations that share the same Core residual, coordinate,
   assembly, ledger, routing, closure, and work-budget machinery;
5. generated catalogs and web evidence whose green status means a direct,
   fresh, kernel-checked Hypostructure source file;
6. no production import from `Hypostructure` to `StructuralExhaustion` or from
   a Hypostructure application to a legacy application;
7. no compatibility aliases, custom handoffs, copied outputs, caller-selected
   routes, or application-defined closure records; and
8. no in-tree legacy implementation after final cutover. Git history is the
   archive.

Framework completion and theorem completion are different milestones. A
complete PDE framework can represent and execute every required fast-track row
without thereby proving every analytic Navier--Stokes input theorem. A final
Navier--Stokes regularity theorem is claimed only when all row contracts are
proved or explicitly imported at the allowed local theorem boundary and the
row-18 target-completeness executor closes every residual.

## 2. Non-negotiable migration rules

These rules apply from the first commit to final deletion of the legacy tree.

### 2.1 Import direction

- `hypostructure/Hypostructure/**` may import Mathlib and other
  `Hypostructure/**` modules only.
- It must never import `StructuralExhaustion`, `Erdos64EG`, a legacy generated
  artifact, or a migration parity module.
- `examples/hypostructure_erdos_64_eg/**` may import Mathlib,
  `Hypostructure`, and its own earlier application modules only.
- `examples/hypostructure_pde/**` has the same rule.
- Only `examples/hypostructure_parity/**` may import both old and new packages.
- Legacy production modules remain frozen and never import Hypostructure.

The import firewall is enforced by a linter before any semantic comparison is
accepted.

### 2.2 Residual and ledger discipline

- There is one root residual per proof program.
- Every later node consumes the exact residual or framework-owned join stage
  emitted by its direct predecessor edge.
- Every inherited fact is retrieved through a typed ledger query.
- Applications never copy a predecessor theorem into a new output record.
- A node adds only its new local semantic fact or invokes one framework
  executor.
- All decisions, sibling preservation, route selection, ledger extension,
  coordinate transport, gluing, and terminal construction are framework
  operations.
- A join with several incoming paper edges is a Core join executor over typed
  predecessor stages. It is not an application tuple of old node outputs.

### 2.3 Trust discipline

- Core, CT, Routes, Graph, and generic PDE modules contain no axioms, `sorry`,
  `admit`, or unsafe declarations.
- Graph external theorems live under `Hypostructure.Graph.External` and are
  exact-name allowlisted.
- PDE analytic imports live under equation-specific
  `Hypostructure.PDE.External.*` namespaces and state local input/output
  contracts.
- No external declaration may assert a final EG theorem, final
  Navier--Stokes theorem, route closure, or target-completeness verdict.
- Every public node endpoint gets a transitive `#print axioms` audit.

### 2.4 No regression laundering

The migration tracks two independent judgments:

1. **Parity:** the new node has the same normalized behavior as the selected
   legacy baseline.
2. **Mathematical closure:** the new node satisfies the manuscript and new API
   contract without an unsupported premise.

A conditional, partial, or yellow legacy node can become parity-checked while
remaining mathematically open. It cannot become green merely because its old
counterpart compiled.

### 2.5 No premature deletion

Legacy declarations remain untouched until the corresponding migration wave
has a new implementation, parity evidence, manuscript evidence, kernel
evidence, and generated metadata. The old tree is deleted only during final
cutover, after the full repository passes both old and new release gates.

## 3. Current repository baseline

The existing implementation has four relevant boundaries:

| Boundary | Current location | Role during migration |
|---|---|---|
| Reference manuscript | `original_erdos_64_proof.tex` | Immutable mathematical strategy, topology, and node-responsibility authority |
| Legacy framework | `lean/StructuralExhaustion` | Frozen implementation reference |
| Legacy EG application | `examples/erdos_64_eg` | Kernel-checked node and parity reference |
| Living manuscript | `proofs/erdos_64_eg/erdos_64_proof.tex` | Non-binding editorial cross-check only |
| Generated/web pipeline | `generated`, `tools`, `web` | Evidence pipeline to duplicate before cutover |

The existing root `Makefile` builds the legacy framework and external examples,
exports catalogs, checks kernel trust, validates schemas, and tests the web UI.
These targets remain authoritative for the baseline until final cutover.

For every EG packet, mathematical requirements and diagram edges are copied
from `original_erdos_64_proof.tex`.  The corresponding kernel-checked legacy
node is then read as implementation and parity evidence.  The living
manuscript may help locate commentary, but it cannot add, remove, strengthen,
weaken, or redirect a migration obligation.

The generated `migration/hypostructure/eg-original-node-anchors.json` may be
used only to locate the exact node command in the pinned original. Its declared
scope is `diagram_anchor_only`; it does not replace reading the surrounding
definitions, theorem statements, continuation prose, or detailed dependency
entry needed to freeze the full quantified contract.

At the time this guide was written, the EG application had direct node facade
files for Nodes 1-64 and 145-164, plus many nested implementation modules. The
compiled export and direct files can temporarily disagree while the worktree is
being developed. They are therefore implementation and parity observations,
not topology authority. Phase 0 still regenerates and freezes their evidence at
a named clean baseline.

For EG specifically, the paper node universe and topology are fixed by the
numbered diagrams and continuation captions of `original_erdos_64_proof.tex`:
exactly Nodes 1-157. The migration updater carries one complete explicit map of
those predecessors. Source-only legacy Nodes 158-164 are recorded in a separate
supplemental evidence inventory and are excluded from the paper DAG, frontier,
and migration-completeness criteria. A compiled example descriptor may mirror
the authoritative map for rendering, but may not infer or change it from Lean
imports.

## 4. Chosen package topology

Hypostructure is an independent root-level Lake package. It is not added as a
second library inside `lean/`, because package separation gives the strongest
possible import firewall and permits independent build, cache, catalog, and
cutover decisions.

```text
hypostructure/
  lakefile.toml
  lean-toolchain
  Hypostructure.lean
  Hypostructure/
    Core/
    CT1/
    CT2/
    ...
    CT17/
    Routes/
    Graph/
    PDE/
    Canonical/
    Fixtures/

examples/
  hypostructure_erdos_64_eg/
    lakefile.toml
    HypostructureErdos64EG.lean
    HypostructureErdos64EG/
  hypostructure_pde/
    lakefile.toml
    HypostructurePDEExamples.lean
    HypostructurePDEExamples/
  hypostructure_parity/
    lakefile.toml
    HypostructureParity.lean
    HypostructureParity/

migration/hypostructure/
  baseline/
  api-feature-matrix.csv
  eg-node-matrix.csv
  pde-row-matrix.csv
  trust-allowlist.json
  decisions/
```

### 4.1 Package names

- Lake package: `hypostructure`
- Lean library: `Hypostructure`
- Root namespace: `Hypostructure`
- New EG package/library: `hypostructure_erdos_64_eg` /
  `HypostructureErdos64EG`
- PDE example package/library: `hypostructure_pde` /
  `HypostructurePDEExamples`
- Test-only comparison package/library: `hypostructure_parity` /
  `HypostructureParity`

CT identifiers remain `CT1` through `CT17`. They identify mathematical tactic
contracts, not the legacy framework brand.

### 4.2 Initial `lakefile.toml`

The new package pins the same Lean and Mathlib versions as the baseline until
the migration is complete:

```toml
name = "hypostructure"
version = "0.1.0"
defaultTargets = ["Hypostructure"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.31.0"

[[lean_lib]]
name = "Hypostructure"
```

The `lean-toolchain` file is copied byte-for-byte from `lean/lean-toolchain` at
bootstrap. Toolchain upgrades are forbidden during migration unless performed
as a separate repository-wide change before a new baseline snapshot.

### 4.3 Production versus parity code

The parity package is disposable test infrastructure. Its bridge types are
allowed to mention both implementations, but they are not API adapters and
must never be imported by Hypostructure or either new application. They are
deleted at final cutover.

## 5. Target module layout

The following tree is the intended ownership map. Files are added only when a
phase reaches them; empty placeholder modules are avoided.

```text
Hypostructure/
  Core/
    Problem.lean
    Progress.lean
    Context.lean
    SemanticEquivalence.lean
    Provision.lean
    Residual/Ledger.lean
    Residual/Stage.lean
    Residual/Query.lean
    Residual/Decision.lean
    Residual/Join.lean
    Coordinate/System.lean
    Coordinate/Path.lean
    Coordinate/Transport.lean
    Assembly/AtomContext.lean
    Assembly/LocalToGlobal.lean
    Response/System.lean
    Response/FiniteTable.lean
    ClosedLedger/Closure.lean
    ClosedLedger/Quotient.lean
    ClosedLedger/Propagation.lean
    Compactness/Extraction.lean
    Budget/Resource.lean
    Budget/Work.lean
    Finite/Enumeration.lean
    Finite/Search.lean
    Finite/Accounting.lean
    Execution.lean
    Routing.lean
    Closure.lean
    Metadata.lean
  CTN/
    Spec.lean
    Capability.lean
    State.lean
    Search.lean
    Execution.lean
    Theorems.lean
    Automation.lean
  Routes/
    Registry.lean
    CT1ToCT2.lean
    ...
  Graph/
    Object.lean
    Finite.lean
    Isomorphism.lean
    Coordinate.lean
    Induced.lean
    Deletion.lean
    Contraction.lean
    Boundary.lean
    Gluing.lean
    Target.lean
    Response.lean
    Progress.lean
    Budget.lean
    CT1.lean
    ...
    CT17.lean
    Theorems/
    External/
  PDE/
    Model.lean
    Atlas.lean
    Equation.lean
    Representation.lean
    Observable.lean
    Coordinate.lean
    LocalTail.lean
    EllipticConstraintTail.lean
    Compactness.lean
    Budget.lean
    ClosedLedger.lean
    FastTrack/
    NavierStokes/
    External/
  Canonical/
    Registry.lean
    Export.lean
    ExampleExport.lean
```

`CTN` above means the same seven-file shape is used for each CT1-CT17 when the
CT needs all layers. Small CTs may combine files only when the dependency
direction remains visible. No `Graph.lean` file lives inside a CT directory;
graph constructors belong under `Hypostructure.Graph`.

## 6. Migration records and status model

Three machine-readable matrices drive the work. They are committed and
reviewed like source code.

### 6.1 API feature matrix

`migration/hypostructure/api-feature-matrix.csv` has one row per required Core,
CT, Route, Graph, or PDE feature:

```text
feature_id,owner,spec_section,legacy_sources,new_module,
first_graph_consumer,first_pde_consumer,fixtures,status,notes
```

Allowed status values:

```text
planned
specified
implemented
kernel_checked
integration_checked
cutover
```

### 6.2 EG node matrix

`migration/hypostructure/eg-node-matrix.csv` has at least:

```text
node_id,paper_ref,direct_predecessors,legacy_files,legacy_declarations,
normalized_input,normalized_outcomes,ct_ids,required_features,new_file,
parity_module,legacy_kernel,new_kernel,parity_status,math_status,
work_status,web_evidence,status,blocker
```

`parity_status` and `math_status` are intentionally separate. `status` uses:

```text
inventoried
scaffolded
typechecked
parity_checked
migrated_open
migrated_closed
published
cutover
```

Only `migrated_closed` nodes are eligible for green proof status. A
`migrated_open` node is a valid Hypostructure translation whose residual still
has an unresolved paper obligation.

### 6.3 PDE row matrix

`migration/hypostructure/pde-row-matrix.csv` tracks notebook rows 1-18,
including row 17b:

```text
row_id,notebook_source,required_capabilities,ct_chain,
axiom_free_fixture,ns2d_instance,complementary_residual,
kernel_status,integration_status,notes
```

### 6.4 Decision records

Any change to the three API specification documents requires a short decision
record under `migration/hypostructure/decisions/`. A decision record states:

- the missing use case;
- why the operation belongs in Core, Graph, PDE, or the application;
- the exact public author inputs;
- the framework-derived outputs;
- every residual branch;
- the Graph and PDE both-sides test;
- fixtures; and
- compatibility impact.

## 7. Validation levels

Validation is layered so node work remains fast without weakening release
checks.

### 7.1 Level A: focused source check

Run after every edited Lean file:

```bash
cd hypostructure
lake env lean Hypostructure/Core/Residual/Ledger.lean
```

For an application node:

```bash
cd examples/hypostructure_erdos_64_eg
lake env lean HypostructureErdos64EG/Node35.lean
```

### 7.2 Level B: package check

```bash
cd hypostructure && lake build
cd examples/hypostructure_erdos_64_eg && lake build
cd examples/hypostructure_pde && lake build
cd examples/hypostructure_parity && lake build
```

### 7.3 Level C: migration integration check

The root `Makefile` gains these additive targets without changing legacy
targets:

```text
hypostructure-framework-build
hypostructure-erdos-build
hypostructure-pde-build
hypostructure-parity-build
hypostructure-lint
hypostructure-kernel
hypostructure-generate
hypostructure-validate
hypostructure-test
migration-test
```

`migration-test` runs the complete legacy `make test`, then the complete
Hypostructure test chain, then cross-implementation parity. It is the required
gate for a migration-wave merge.

### 7.4 Level D: release check

Before a published status change or cutover:

- both package trees build from a clean cache state;
- all generated files are regenerated and byte-fresh;
- every schema validates;
- all Python and frontend tests pass;
- every direct node source has a fresh `.olean`;
- all required `#print axioms` results match the allowlist;
- the import firewall has no violation; and
- the web backend starts from regenerated evidence without stale-hash mode.

## 8. Parity model

Parity compares public mathematical behavior, not proof terms or private
record layouts.

### 8.1 Normalized observations

For each migrated node, define a test-only normalized observation containing
only paper-visible facts:

```lean
structure NodeObservation where
  branchTag : BranchTag
  targetClosed : Prop
  residualPredicate : NormalizedResidual -> Prop
  publicFacts : PublicFactCode -> Prop
```

The actual observation type is node-specific and may be dependent. It must not
contain old/new implementation records, proof terms, ledger list shapes, or
private constructor names.

### 8.2 Required parity theorems

Each node parity module proves the applicable subset of:

- official input equivalence;
- baseline equivalence;
- target equivalence;
- branch partition equivalence in both directions;
- target-terminal equivalence;
- residual predicate equivalence;
- public local-fact equivalence;
- predecessor preservation;
- work-bound comparison; and
- trust-boundary equality.

Finite fixtures additionally compare deterministic branch tags and computed
codes by evaluation. General parity is theorem-level and does not rely only on
testing examples.

### 8.3 Test-only bridges

When old and new ambient or residual types differ, the parity package defines
an explicit relation rather than a production conversion function. It proves
that both objects represent the same Mathlib graph, target, support, boundary,
or local PDE state. The relation is deleted at cutover.

### 8.4 Parity is not authority

If the legacy node has an unsupported input, copied output, custom handoff, or
conditional gap, the new node does not reproduce that defect as an assumption.
It emits the exact open residual prescribed by the manuscript. The parity
record documents the deliberate difference and `math_status` remains open
until a real producer closes it.

### 8.5 Apparent gaps in the immutable EG source

If formalization reveals that a statement or proof step in
`original_erdos_64_proof.tex` does not follow from its written hypotheses, do
not repair it from the living manuscript, a future file, or a stronger legacy
structure. Apply this protocol:

1. Reconstruct the exact statement, quantifiers, definitions, and incoming
   edges from the original source.
2. Reduce the failure to the smallest domain-generic obligation.
3. When finite, add a kernel-checked counterexample or independence fixture in
   `Hypostructure.Fixtures`; otherwise record the failed proof obligation
   exactly.
4. Record the issue in a separate migration document, including any hidden
   premise found in legacy implementation evidence.
5. Implement reusable framework machinery for the honest strengthened
   contract or for a typed complementary residual, but do not instantiate that
   strengthening as an original-paper fact.
6. Leave the paper node `math_status=open` and its downstream frontier closed.
7. Require an explicit approved correction before changing the migration
   theorem statement or adding a premise not present in the original.

The immutable source itself is never edited by the migration. A checked
legacy proof under a stronger representation establishes implementation
evidence for that stronger representation, not the original theorem.

## 9. Phase 0: freeze a trustworthy baseline

No Hypostructure implementation begins until the legacy baseline is
reproducible.

### 9.1 Select the baseline revision

1. Start from a named Git commit, not an unrecorded dirty worktree.
2. Record the commit hash, Lean toolchain, Mathlib revision, Python lock/input
   files, Node lockfile hash, and source date.
3. Tag the revision with a name such as
   `hypostructure-migration-baseline-YYYYMMDD`.
4. If the current worktree contains desired uncommitted proof work, commit it
   first as an ordinary legacy change and rerun the baseline gate.

### 9.2 Regenerate the legacy evidence

Run, in order:

```bash
make framework-build
make erdos-example-build
make generate
make kernel
make validate
make web-test
make test
```

Do not use `STRUCTURAL_EXHAUSTION_ALLOW_STALE_HASHES=1` for this snapshot.

### 9.3 Capture baseline artifacts

Copy the following generated values into
`migration/hypostructure/baseline/` with a manifest and hashes:

- `generated/kernel-verification.json`;
- `generated/lean-machines.json`;
- `generated/framework-documentation.json`;
- `generated/examples/erdos-64.json`;
- `generated/examples/erdos-64-history.json`;
- the raw EG export used to hydrate the catalog;
- `generated/node-index.csv`;
- the exact trusted-axiom allowlist;
- direct EG `NodeX.lean` source hashes;
- direct EG `.olean` freshness/status;
- public declaration names used by WebExport; and
- per-node work bounds when present.

The snapshot manifest records whether each artifact came from a clean build.
Generated files that disagree with source are fixed before capture, not
silently accepted as baseline behavior.

### 9.4 Build a topology inventory

Extract the following topology and mathematical fields exclusively from
`original_erdos_64_proof.tex`:

- every paper node ID;
- direct incoming and outgoing edges;
- closure leaves;
- active residual leaves;
- node-to-proof-step evidence;
- and the responsibility assigned to each node.

Then attach observational fields from the kernel-checked legacy source and
WebExport without allowing those sources to alter the paper graph:

- node-to-CT implementation use;
- node-to-source declaration bindings;
- direct source and `.olean` freshness;
- parity-facing declarations; and
- every current implementation-side partial obligation.

Store Nodes 1-157 in the EG node matrix. Store source-only legacy nodes in the
supplemental evidence inventory, which has no paper status, frontier, or
completeness fields. Numeric order is not treated as topological order. For
example, Nodes 65 and 89 have feedback inputs, and join nodes may depend on more
than one earlier paper edge.

### 9.5 Phase 0 exit gate

Phase 0 is complete only when:

- `make test` passes at the selected baseline;
- the web backend loads the regenerated EG artifact;
- every non-missing obligation has valid evidence;
- direct node status agrees with fresh `.olean` files;
- the baseline manifest is committed; and
- later legacy changes require an explicit baseline-refresh decision.

## 10. Phase 1: create the independent package and firewall

This phase creates infrastructure only. It does not copy CT implementations.

### 10.1 Package bootstrap

Create:

- `hypostructure/lakefile.toml`;
- `hypostructure/lean-toolchain`;
- `hypostructure/Hypostructure.lean`;
- `hypostructure/Hypostructure/Core/Prelude.lean`; and
- one trivial compile fixture under `Hypostructure/Fixtures`.

The root import initially imports only `Core.Prelude`. It grows by reviewed
public modules; it never imports all internal fixtures.

### 10.2 Import linter

Add a Hypostructure linter that checks:

- no source under `hypostructure/Hypostructure` imports a module beginning
  with `StructuralExhaustion` or `Erdos64EG`;
- no generic source imports `HypostructureErdos64EG` or
  `HypostructurePDEExamples`;
- a producer CT does not import a consumer CT;
- Routes may import source and target public CT interfaces only;
- Graph and PDE may import Core and CTs, but Core and CTs may not import Graph
  or PDE;
- external axioms occur only at exact allowlisted files and declaration names;
- `Future`, `Legacy`, `Compat`, `ExactHandoff`, and non-executable semantic
  handoff modules do not appear in production imports; and
- no generated source is imported as mathematical authority.

### 10.3 Build integration

Add the new Make targets from Section 7. Existing targets must retain their
behavior and output paths. At this phase `migration-test` proves that the empty
new package does not disturb the legacy system.

### 10.4 Phase 1 exit gate

- New package builds independently.
- The import linter has positive and negative tests.
- Legacy `make test` is unchanged and passes.
- Hypostructure generated output paths are separate from legacy paths.
- No API alias from `StructuralExhaustion` exists.

## 11. Phase 2: implement the irreducible Core

Implement the minimum Core needed to define both an EG problem and a PDE
problem. Follow `DOMAIN_INDEPENDENT_CORE.md` exactly.

### 11.1 Problem and target

Implement `Hypostructure.Core.Problem` with only:

```text
Ambient
Baseline
BranchState
```

Keep `Target` external. Do not put rank, graph size, topology, measure,
equation, or target into `Problem`.

Add compile fixtures showing:

- one ambient type with two different targets;
- a problem with no progress measure;
- a problem with a nontrivial dependent branch state; and
- no graph or PDE import in the dependency cone.

### 11.2 Optional progress

Implement `Core.Progress` with a well-founded relation and measure. Prove the
generic smaller-object contradiction once. Test:

- natural-number progress;
- lexicographic progress;
- a no-progress CT fixture that does not require an instance; and
- rejection of a non-strict replacement.

### 11.3 Context hierarchy

Implement:

- `BranchContext`;
- `AvoidingContext`;
- `MinimalCounterexampleContext`; and
- constructors that derive, rather than accept, target and minimality
  consequences.

Context construction must not duplicate the residual ledger. Contexts contain
the current ambient object, baseline proof, and irreducible branch state only.

### 11.4 Semantic equivalence

Implement `Core.SemanticEquivalence` and `Core.TargetInvariant`.

Required fixtures:

- equality equivalence;
- a finite relabeling equivalence with an invariant target;
- an additive quotient relation suitable for a pressure gauge toy; and
- a failing target-invariance example that cannot be transported.

### 11.5 Proof ledger

Implement the dependent proof ledger before any CT:

- one literal residual carrier;
- proposition nodes;
- data-bearing stage nodes;
- typed `LedgerQuery`;
- predecessor retention;
- no-copy extension;
- exact duplicate handling policy;
- focused branch lookup; and
- proof that extending the ledger preserves every prior query.

The implementation may use a dependent list, nested sigma type, or equivalent
representation, but its public API exposes only typed construction and query.

Implement `Core.Residual.ProofProjection` for a node that derives one
predecessor-indexed proposition from an exact active query without inspecting
new primitive data. Core owns its private certificate, focused execution,
ledger extension, latest queries, inactive outcome, and definitionally zero
local projection work. Its total executor budget is exactly the counted
selection budget inherited from the focus. The application supplies only the
dependent claim and proof query. A proof projection is not a substitute for a CT search or a binary
decision: any new inspection or alternative must use the corresponding
framework executor.

Required negative tests:

- a query for an absent fact does not elaborate;
- a stage for a different residual cannot be inserted;
- a successor cannot replace the residual carrier;
- a sibling fact is still retrievable after focused continuation; and
- a copied application output is unnecessary in all fixtures.

The proof-projection fixture additionally checks active and inactive
execution, exact latest-query retrieval, literal predecessor and root-residual
retention, one counted structural focus selection, and zero additional
projection work.

### 11.6 Decision and join primitives

Implement framework-owned:

- exhaustive binary decision;
- dependent yes/no continuation;
- close-one-side-and-continue-the-other;
- nested focused continuation;
- sibling preservation;
- terminal attachment; and
- typed multi-predecessor join.

Every decision records both outcomes before focus. Every join states the exact
compatibility theorem between incoming residuals and preserves all incoming
ledgers through framework code.

### 11.7 Core bootstrap fixtures

Create non-domain fixtures for:

- Boolean decision and both branches;
- a three-step predecessor chain;
- a branch split followed by independent advancement;
- a branch join;
- typed retrieval of the root fact at the final node; and
- a terminal contradiction that cannot be caller-selected.

### 11.8 Phase 2 exit gate

- All Core bootstrap modules are axiom-free.
- Graph and PDE imports are absent.
- Every decision and join fixture passes `#print axioms`.
- The public node shape is already
  `executor previousResidual localCertificate`.
- No CT, Graph, or PDE behavior has been smuggled into Core names.

## 12. Phase 3: coordinates, assembly, closed ledgers, and budgets

This phase implements the shared machinery needed by both domain layers before
either domain defines complex tactics.

### 12.1 Coordinate system

Implement:

- primitive coordinate generators;
- coordinate-indexed object families;
- realization into the ambient problem;
- identity path;
- path composition;
- path execution;
- baseline transport;
- branch-state transport;
- target naturality;
- obstruction transport;
- ledger-stage transport; and
- progress-effect composition.

Applications may provide primitive parameters but never invoke raw `act`,
`append`, or transport operations.

Required cross-domain fixtures:

- graph relabel then induced restriction;
- scalar field translation then scaling;
- pressure gauge normalization then quotient projection; and
- a two-step path whose composite preservation theorem is obtained entirely
  from Core.

### 12.2 Locality

Implement nested windows, restriction, nested restriction, and exact support
ownership. Core does not assume a finite point set. Finite scans require an
explicit residual-owned family.

Fixtures:

- finite subset restriction;
- nested interval restriction;
- a pointwise local closure with no global enumeration; and
- rejection of a window not proved nested.

### 12.3 Interface-indexed atom/context assembly

Implement dependent interfaces, atoms, contexts, compatibility, assembly, and
reconstruction up to `SemanticEquivalence`.

Core derives:

- extraction of the current atom and context;
- compatible replacement;
- response transport through assembly;
- exact recombination;
- progress verification; and
- terminal or residual routing.

Fixtures must include both:

- finite boundaried graph union up to isomorphism; and
- additive local term plus tail equality.

### 12.4 Generic response algebra

Implement in Core, not Graph:

- representatives and signed progress increment;
- finite response coordinates;
- exact finite response vectors;
- symbolic outside-context coverage;
- distinction versus universal neutrality;
- target-complete equivalence; and
- conditional orientation after nonzero progress.

This is the target owner of the reusable algebra currently embedded in legacy
`FiniteContextResponseComparison` and `FiniteSameInterfaceExchange` modules.

### 12.5 Closed-class ledger

Implement:

- abstract closure operators;
- target-null closed-class ledgers;
- domain-registered quotient universal properties;
- canonical projection;
- ledger extension;
- quotient-compatible transport;
- iterative propagation; and
- the no-rechecking theorem.

Fixtures:

- identity closure on a finite type;
- equivalence-class quotient;
- additive quotient by constants;
- two sequential ledger propagations; and
- proof that a later invariant factors through the accumulated quotient.

### 12.6 Compact extraction

Implement the dependent extraction package with:

- input sequence;
- strictly increasing selector;
- extracted subsequence identity;
- limit;
- declared topology;
- convergence theorem;
- baseline closure;
- obstruction persistence; and
- descendant residual creation.

The first fixture uses a finite eventually constant sequence. It tests the
machinery without importing a hard analytic compactness theorem.

### 12.7 Resource and work budgets

Implement separate APIs for:

- mathematical resource budgets; and
- verifier work budgets.

Resource budgets include the B1-B4-style composition, representation
invariance, and static/dynamic comparison laws. Work budgets include finite
scan, nested scan, route, and composition accounting.

Never use a verifier work count as a mathematical capacity proof or vice
versa.

### 12.8 Closure and reduction

Implement the five generic closure mechanisms:

- direct target or contradiction;
- strict progress/minimality;
- budget or capacity contradiction;
- exact imported theorem contract; and
- acyclic reduction to an already closed obstruction.

The reduction executor verifies the destination closure, obstruction
transport, coordinate compatibility, and strict routing rank. A matching name
or isomorphic-looking record is insufficient.

### 12.9 Phase 3 exit gate

- One graph and one analytic toy use the same coordinate executor.
- One graph and one analytic toy use the same assembly executor.
- Closed classes propagate twice without rechecking.
- Compact extraction retains an obstruction in a typed descendant.
- Resource and work budget APIs have disjoint types.
- No application-authored route or successor exists in fixtures.

## 13. Phase 4: finite execution kernel and canonical metadata

The CTs need a common execution substrate before they are translated.

### 13.1 Finite primitives

Implement or wrap Mathlib facilities for:

- explicit `FinEnum` order;
- ordered partial collections;
- first-hit search;
- exhaustive scan;
- product and subtype enumeration;
- exact finite counts;
- finite fibres;
- first failure;
- deterministic tie-breaking;
- disjoint packing; and
- bounded work composition.

Do not introduce a parallel finite-set theory. Use Mathlib `Finset`, `Fintype`,
and graph definitions wherever their semantics suffice.

### 13.2 Generic execution result

Every CT execution exposes:

- exact input indexed by predecessor context;
- typed outcome;
- trace;
- soundness;
- totality;
- deterministic reference semantics;
- outcome exhaustiveness;
- visible check count;
- polynomial work proof where required; and
- accumulated residual stage.

### 13.3 Capability authoring boundary

The canonical metadata records for each executable node:

- primitive author inputs;
- inferred dependencies;
- ordinary predecessor ledger queries;
- proof-indexed predecessor queries on framework-owned focused branches;
- framework search;
- generated states and residuals;
- generic theorems;
- work bound; and
- remaining manual obligations.

A completed framework node has an empty manual-obligation list. Mathematical
application obligations are residuals, not metadata exceptions.

### 13.4 Initial exporter

Create a separate catalog at:

```text
generated/hypostructure/lean-machines.json
generated/hypostructure/framework-documentation.json
generated/hypostructure/kernel-verification.json
```

Do not overwrite legacy catalogs. Preserve stable CT IDs but add a framework
identity/version field so the web backend cannot mix declarations from the two
implementations.

### 13.5 Phase 4 exit gate

- Finite search fixtures cover every branch.
- Metadata is derived from compiled Lean declarations.
- Export is deterministic and byte-fresh.
- Kernel verification rejects one intentionally malformed test fixture.
- No catalog entry can claim a source declaration that does not elaborate.

## 14. Phase 5: minimal Graph layer and EG problem registration

This phase defines graph semantics and the EG problem, but does not yet migrate
the full EG proof.

### 14.1 Packed finite graph object

Implement the canonical existentially packed finite graph object with:

- a vertex type;
- a Mathlib `SimpleGraph`;
- explicit `FinEnum` vertices; and
- a decidable adjacency relation.

Derive, without application fields:

- ordered vertices, neighbours, edges, and darts;
- vertex and edge counts;
- degree, minimum degree, and maximum degree;
- induced subtype enumerations; and
- deterministic graph scan order.

A fixed-vertex view may exist as an internal convenience, but there is one
mathematical graph representation.

### 14.2 Isomorphism semantics

Instantiate `Core.SemanticEquivalence` by finite graph isomorphism. Prove:

- equivalence laws;
- finite cardinality invariance;
- degree and edge-count invariance;
- baseline transport for baseline profiles that declare invariance; and
- target transport only through an explicit `Graph.TargetInterface`.

### 14.3 Primitive graph coordinates

Implement the graph semantics for:

- relabeling;
- rooting/marking without changing adjacency;
- induced restriction;
- vertex deletion;
- edge deletion;
- contraction; and
- piece replacement.

Core owns coordinate paths. Graph proves only each primitive's adjacency,
support, size, boundary, and isomorphism laws.

### 14.4 Boundary and gluing

Implement:

- labelled finite boundaries;
- pieces with internal vertices;
- finite outside contexts with the same labelled boundary;
- possibly overlapping boundary-edge ownership;
- literal graph union on a sum vertex type;
- reconstruction isomorphism;
- boundary-degree transport;
- internal baseline preservation profiles; and
- exact local/global size changes.

Instantiate `Core.AtomContextAssembly`; do not expose a graph-specific routing
or handoff API.

### 14.5 Minimal graph targets

Implement reusable target encodings for:

- a cycle satisfying a length predicate;
- a path satisfying a predicate;
- graph coloring; and
- direct finite certificate validation.

Only the cycle target is required for initial EG registration. Others are
small independent validators for the API.

### 14.6 Graph bootstrap fixtures

Before defining EG, kernel-check:

- an empty graph and one-vertex graph;
- `K4` finite object enumeration;
- an induced subgraph and embedding;
- relabeling invariance;
- edge deletion and exact edge-count decrease;
- a two-boundary gluing reconstruction;
- a replacement preserving a declared baseline; and
- a direct four-cycle target certificate.

### 14.7 New EG application package

Create `examples/hypostructure_erdos_64_eg` depending only on
`hypostructure` and the pinned Mathlib revision.

Initial modules:

```text
HypostructureErdos64EG/
  OfficialStatement.lean
  TargetAlgebra.lean
  Problem.lean
  InitialResidual.lean
  Fixtures/K4.lean
```

`OfficialStatement.lean` repeats the exact pinned public proposition and source
hash in the new namespace. It does not import the legacy EG package. The parity
package proves equivalence with `Erdos64EG.OfficialStatement`.

### 14.8 EG minimum registration

Define only:

- executable `PowerOfTwoLength`;
- equivalence with the unbounded exponent formulation;
- minimum-degree-three baseline;
- power-of-two-cycle target;
- graph-isomorphism target invariance;
- initial branch state;
- initial residual containing only the graph and hypotheses of the official
  theorem statement; and
- official/internal target equivalence.

A sufficiently-large-tail condition is not accepted as root data. If an
asymptotic argument needs it, the application first uses framework machinery
to close the finite exceptional range and derives the tail condition on the
surviving residual.

Do not copy the legacy `MinimumDegreeCycle.StaticInput` aggregate. Construct the
new Core problem and separate target through the minimal Graph API.

### 14.9 EG registration parity

The parity package proves:

- old and new official statements are equivalent;
- old and new executable length predicates are equivalent;
- baselines agree on the same Mathlib graph;
- targets agree on the same graph;
- finite graph packing does not change the public proposition; and
- the `K4` target certificate has the same public witness.

### 14.10 Phase 5 exit gate

- EG problem definition compiles without any legacy import.
- Graph Core is axiom-free.
- The only EG-specific data are the target predicate, threshold three,
  executable target algebra, and root theorem data.
- The graph gluing fixture and additive PDE assembly fixture use the same Core
  assembly API.
- Official-statement parity is kernel-checked.

## 15. Phase 6: minimal PDE layer and two-dimensional Navier--Stokes

This phase establishes a real PDE-facing API before EG-driven expansion can
overfit Core to graph proofs.

### 15.1 Generic PDE model

Implement the minimal declarations from `PDE_LAYER_API.md`:

- `LocalAtlas`;
- `RepresentedEquation`;
- `LocalModel` containing only problem, atlas, and equation;
- external target predicates;
- optional `ObservableInterface`;
- optional covering profile; and
- PDE representation semantics.

Target, compactness, generator forms, budgets, observables, gauges, and
fast-track rows are independent capabilities, not mandatory `LocalModel`
fields.

### 15.2 PDE coordinate primitives

Register semantics for:

- restriction;
- recentering;
- rescaling;
- normalization/gauge action;
- quotient projection; and
- subsequence extraction.

Each primitive proves only target-independent equation and representation
laws. Target naturality, retained obstruction, and progress effects are
optional theorem-relative profiles.

### 15.3 Axiom-free PDE fixture ladder

Build these fixtures in order:

1. **Additive local/tail fixture.** A function on a finite type decomposes as
   a supported local term plus its complement. Core performs assembly.
2. **Nested-window fixture.** Restriction from a larger finite interval to a
   smaller interval composes exactly.
3. **Recenter/rescale fixture.** A scalar function undergoes two primitive
   coordinate changes; Core proves path composition.
4. **Gauge quotient fixture.** Real-valued functions modulo constants exercise
   semantic equivalence, target invariance, closed ledger, and quotient.
5. **Finite cell budget fixture.** A negative finite sum is localized without
   any graph vocabulary.
6. **Compact extraction fixture.** An eventually constant sequence produces a
   typed extracted descendant with retained obstruction.
7. **Pointwise assembly fixture.** Local closure at each supplied point yields
   a global statement without enumerating an ambient continuum.

Every fixture is axiom-free and has at least one complementary residual test.

### 15.4 Two-dimensional Navier--Stokes model scope

Create a model registration under either
`Hypostructure.PDE.NavierStokes` or the PDE example package according to the
ownership rule:

- equation semantics reusable across proofs belong in the PDE package;
- theorem-specific constants and row data belong in the example package.

The initial model specifies:

- spatial points as a two-dimensional real Euclidean space or a precisely
  chosen periodic two-dimensional domain;
- time and space-time points;
- velocity valued in two-dimensional vectors;
- scalar pressure;
- viscosity;
- nested parabolic or time-space windows;
- restriction to a window;
- divergence-free condition;
- represented weak or smooth Navier--Stokes equation, with the regularity
  class stated explicitly;
- pressure equivalence modulo functions of time or the selected gauge;
- baseline solution contract;
- local regularity target; and
- the coordinate laws for translation, parabolic scaling, restriction, and
  pressure normalization that are actually proved at this phase.

Do not use an ambiguous `Solution` proposition. Its fields must state the
equation interpretation, regularity, divergence, pressure representative, and
domain needed by downstream theorems.

### 15.5 Initial 2D fixtures

Kernel-check at least:

- the zero velocity/zero pressure solution satisfies the selected baseline;
- pressure shifted by an allowed time gauge is semantically equivalent;
- the local regularity target is invariant under the registered equivalence;
- restriction of the zero solution is the zero local solution;
- recentering and rescaling the zero solution compose through Core;
- a trivial local/tail pressure split reconstructs exactly; and
- the model can seed one root residual and ledger without a theorem-specific
  route.

These tests validate representation, not the general 2D regularity theorem.

### 15.6 Analytic import boundary

Create `Hypostructure.PDE.External` infrastructure but add no imported theorem
until a concrete fixture needs it. Each import records:

- stable source ID;
- exact local input;
- exact output;
- locality;
- representative/gauge status;
- convergence topology when relevant;
- retained-obstruction transport; and
- an exact axiom allowlist entry.

A standard 2D existence or regularity theorem, if initially treated as a black
box, is one local external contract. It cannot be the target-completeness
executor or a final theorem axiom.

### 15.7 Phase 6 exit gate

- Generic PDE imports no Navier--Stokes-specific module.
- The 2D model is definable without legacy framework imports.
- All toy fixtures and the zero-solution fixture are axiom-free.
- Gauge and coordinate transports are framework-owned.
- No claim of general 2D regularity is exported unless actually proved.
- Core changes made for PDE are also exercised by a graph fixture where
  semantically applicable.

## 16. Phase 7: implement CT1-CT17 as vertical slices

CT migration is behavior-preserving but not source-copying. Each CT is rebuilt
from its generic contract and tested in both domains where possible.

### 16.1 Mandatory CT shape

For each `CTN`, implement in dependency order:

1. `Spec`: mathematical predicates and types;
2. `Capability`: minimal primitive author inputs;
3. `State`: predecessor-indexed certificates and residuals;
4. `Search`: deterministic reference algorithm;
5. `Execution`: outcome and typed trace;
6. `Theorems`: soundness, totality, determinism, and exhaustiveness;
7. `Automation`: public executor and metadata contract;
8. Graph and PDE constructors in their domain packages;
9. at least one positive and every complementary residual fixture; and
10. parity against the legacy CT on a neutral finite fixture when practical.

### 16.2 CT implementation order

Use the first real consumers to force complete vertical slices:

| Wave | CTs | Reason |
|---|---|---|
| CT-A | CT1, CT2, CT3 | Target validation, minimal deletion, and atom/context response are the first EG proof block and foundational PDE operations |
| CT-B | CT12, CT10, CT15 | Packing, finite classification, and target-relative rank drive early EG structure and PDE quotient checks |
| CT-C | CT4, CT5, CT6, CT9 | Assignment, aggregation, ordered failure, and fibre overload provide shared accounting |
| CT-D | CT11, CT13, CT14 | Deficit localization, fallback routing, and aggregate capacity support later EG and PDE budget rows |
| CT-E | CT7, CT8, CT16, CT17 | Context distinction, repetition, whole-support closure, and bounded target arithmetic complete the structural family |

Within a wave, implement only the first dependency-ready CT, finish all its
outcomes and fixtures, then continue. Do not scaffold seventeen incomplete
machines at once.

### 16.3 Cross-domain validation matrix

| CT | First graph validator | First PDE/neutral validator |
|---|---|---|
| CT1 | Explicit `K4` cycle certificate | Explicit local target or zero-capacity toy certificate |
| CT2 | Edge deletion or boundaried replacement | Strictly smaller local atom toy |
| CT3 | Same-boundary graph response | Additive local/tail or gauge response |
| CT4 | Color/charge payer assignment | Error demand to finite window account |
| CT5 | Local graph contribution ledger | Local energy/flux contribution ledger |
| CT6 | Ordered graph site failure | First failed row/window schedule |
| CT7 | Distinguishing outside graph context | Distinguishing tail or gauge context |
| CT8 | Repeated finite interface type | Repeated scale/profile toy state |
| CT9 | Overloaded graph label fibre | Too many packets for finite mass capacity |
| CT10 | Attachment/local-type classifier | Residual-signature classifier |
| CT11 | Negative dart/support budget | Negative finite cell/integral component budget |
| CT12 | Vertex/support peeling or packing | Finite profile/dyadic peeling toy |
| CT13 | Primary payer then fallback | Local/harmonic or gauge/cokernel fallback toy |
| CT14 | Support mass versus multiplicity | Profile mass or capacity aggregation |
| CT15 | Boundary/response rank | Gauge cokernel or quotient rank toy |
| CT16 | Whole finite support code | Final compactified finite-class audit toy |
| CT17 | Bounded cycle length/offset | Bounded scale or target-shell arithmetic |

No PDE fixture is required to pretend that a genuinely graph-only semantic
lemma has a PDE meaning. The shared test is the Core CT contract; domain
bridges remain honest.

### 16.4 Route migration

Rebuild framework-owned route profiles only after both source and target CT
executors exist. The old generated registry, rather than the shorter prose
list that preceded this migration, is the compatibility baseline. It contains
29 executable profiles in 28 source/target families.

The nine specialized profiles have semantic discovery beyond a generic
ledger extension:

- CT1 to CT2, with distinct ordinary and local-deletion profiles;
- CT1 to CT12;
- CT2 to CT3;
- CT2 to CT10;
- CT5 to CT14;
- CT6 to CT9;
- CT9 to CT7; and
- CT14 to CT14 refinement.

The following twenty edges use one reusable accumulated-transition executor.
They are registry data, not twenty copies of route plumbing:

```text
CT1  -> CT9       CT1  -> CT10      CT2  -> CT1
CT3  -> CT1       CT5  -> CT2       CT7  -> CT5
CT5  -> CT10      CT9  -> CT1       CT9  -> CT5
CT9  -> CT10      CT9  -> CT14      CT10 -> CT5
CT10 -> CT6       CT10 -> CT9       CT10 -> CT14
CT12 -> CT10      CT12 -> CT15      CT14 -> CT1
CT14 -> CT12      CT15 -> CT9
```

Port the accumulated executor once into `Core.Routing`, then register those
twenty edges in `Routes.Registry`. Specialized discovery profiles remain in
their own `Routes/CTxToCTy.lean` modules.

The legacy EG implementation also reveals routes that were application-owned
and therefore were never registered correctly: CT12 to CT6, CT6 to CT15,
CT15 to CT15, and two semantically distinct CT9 to CT9 refinements. They are
requirements for the new registry, not patterns to copy into EG node files.

The PDE architecture requires the following additional registered families:

```text
CT15 -> CT16      CT15 -> CT10      CT13 -> CT7
CT3  -> CT7       CT17 -> CT12      CT12 -> CT11
CT10 -> CT11      CT11 -> CT14      CT14 -> CT11
CT3  -> CT14      CT14 -> CT15      CT15 -> CT13
CT11 -> CT1       CT14 -> CT16      CT16 -> CT10
CT7  -> CT16      CT16 -> CT1       CT3  -> CT13
CT13 -> CT15      CT15 -> CT14
```

These edges are implemented only when both endpoint contracts exist. A CT
chain in a paper or PDE row is never permission for application code to
construct the next CT input directly.

Each route:

- accepts the complete accumulated source residual stage;
- performs semantic discovery through a domain capability;
- constructs the target input internally;
- runs the public target executor;
- preserves the exact predecessor;
- records provenance;
- returns the target-labelled accumulated ledger; and
- exposes every disabled or failure branch as a typed residual.

Do not migrate the legacy non-executable `SemanticHandoffContract` as a public
escape hatch. Any recurring handoff becomes an executable generic Core or
domain profile with real residuals and tests.

### 16.5 CT wave exit gate

A CT wave is complete only when:

- every constructor and residual is tested;
- all public theorems are kernel-checked;
- work bounds compose;
- metadata exports are fresh;
- no manual-obligation field is hidden;
- at least one non-EG fixture exercises each generic executor; and
- every route in the wave preserves full-ledger queries from its source.

## 17. Phase 8: migrate the EG proof node by node

Node migration starts after the Core, minimal Graph/PDE models, and the CTs
needed by the first node are ready. Framework functionality is then expanded
just in time, always generically.

### 17.1 One-node work packet

Each node is migrated in a separate reviewable work packet:

1. Open `original_erdos_64_proof.tex` and, before consulting any other EG
   source, extract the node's exact quantified hypotheses, inherited facts,
   branch alternatives, terminal or residual meaning, incoming edges, and
   outgoing edges. Record the diagram part, bracketed node ID, and every
   theorem/definition label cited by that node as its immutable source locator.
   The generated diagram-anchor registry may locate the node's exact TeX
   command, but its `diagram_anchor_only` entry is never the complete contract.
2. Freeze that original-derived contract in the work packet. The living
   manuscript, repair notes, generated metadata, and Lean imports may not add,
   remove, strengthen, weaken, or redirect any part of it.
3. Only then read the matching kernel-checked legacy `NodeX.lean` facade and
   every declaration in its dependency cone, solely as implementation and
   parity evidence.
4. Identify the literal predecessor residual and all facts the node uses.
5. Classify every used fact as root data, predecessor payload, ledger query,
   domain theorem, external theorem, or unsupported legacy assumption.
6. Select the CT or Core executor from the specification.
7. Record any missing generic feature in the API feature matrix.
8. Implement that feature at the lowest correct owner with independent
   fixtures before touching the node.
9. Implement the new node as a thin executor call.
10. Prove all branch and public-fact parity theorems.
11. Audit transitive axioms and work bounds.
12. Add compiled metadata and web evidence.
13. Update `parity_status`, `math_status`, and migration status independently.

### 17.2 Required node file shape

A normal node imports:

- its direct predecessor facade or framework-owned incoming join;
- problem-local definitions genuinely needed for its new theorem; and
- the smallest public Hypostructure module exposing its executor.

Conceptually:

```lean
noncomputable def nodeN :=
  Hypostructure.SomeExecutor.advance previousResidual
    localSemanticCertificate
```

It must not define:

- a copied predecessor output;
- a custom output carrying inherited facts;
- a local route enum;
- a custom handoff;
- an empty replacement ledger;
- a manually transformed graph;
- a caller-selected CT outcome; or
- an assumed closure payload.

### 17.3 Framework-gap protocol

When a node cannot be thinly expressed:

1. Stop application work.
2. State the missing operation without EG names or constants.
3. Apply the both-sides test: identify a graph and PDE/neutral interpretation.
4. Decide ownership:
   - no graph/PDE vocabulary: Core or generic CT;
   - graph semantics only: Graph;
   - analytic semantics only: PDE;
   - `P13`, fan, shoulder, port, fixed coefficient, or paper branch: EG app.
5. Add a decision record.
6. Implement the generic executor and all residuals.
7. Add an independent fixture, preferably one from the other domain.
8. Register metadata and work bounds.
9. Resume the node using only the public executor.

An operation is not generic merely because its type parameters have generic
names. Its assumptions and conclusions must make mathematical sense outside
the motivating EG node.

### 17.4 Node parity gate

A node reaches `parity_checked` only if:

- the same official/root input is related;
- every old public branch has a new normalized counterpart or a documented
  manuscript-correct repair;
- every new branch is prescribed by the manuscript/framework contract;
- predecessor and root facts remain queryable;
- direct target and contradiction closures agree;
- finite deterministic outputs agree on golden fixtures;
- work is no worse asymptotically unless justified; and
- the new node imports no legacy module.

### 17.5 Mathematical gate

A node reaches `migrated_closed` only if:

- its exact paper-local responsibility is proved;
- no unsupported premise was added;
- every complementary residual has a registered consumer or is an explicit
  active frontier;
- every closure is C1-C5/direct-target/minimality/budget/imported-theorem/
  acyclic-reduction justified through Core;
- all required facts come from the predecessor ledger; and
- `#print axioms` matches the allowed trust boundary.

### 17.6 Suggested EG migration waves

The waves are planning buckets. Actual order follows the immutable DAG in
`original_erdos_64_proof.tex`.

| Wave | Nodes/responsibility | Expected framework pressure |
|---|---|---|
| EG-0 | Official statement, target algebra, problem, initial residual | Core Problem, Graph object/target |
| EG-1 | Nodes 1-3 | Root ledger and counterexample decision |
| EG-2 | Nodes 4-10 | Minimal selection, CT1, CT2, deletion criticality |
| EG-3 | Nodes 11-16 | Boundary assembly, CT3, HSS external theorem, CT1 closure |
| EG-4 | Nodes 17-24 | CT12 packing, CT10 labels, finite threshold and sequential ledger |
| EG-5 | Nodes 25-47 | Remainder support, CT14/CT15, rank split, response and whole-support closure |
| EG-6 | Nodes 48-64 | Entropy, product/budget transfer, sign split, CT11 localization, branch routing |
| EG-7 | Original nodes 65-144 | Type A/B, fans, ports, charging, matching, role fibres, and classifier blocks |
| EG-8 | Original Nodes 145-157 | Route-8 threshold and cold-branch chain through the three terminal germ cases |

EG-7 requires special care because substantial legacy work is currently
packaged in shared modules rather than one direct facade per paper node. The
new application creates one direct `NodeX.lean` facade only when that node's
literal producer and evidence are migrated. It does not mark a numeric range
green from one aggregate theorem.

Legacy Nodes 158-164 are not an EG migration wave. They remain supplemental
implementation/parity evidence unless and until a distinct, explicitly scoped
non-paper theorem is specified; they never count toward completion of the
original EG DAG.

The current worktree theorem `Erdos64EG.Internal.only_type_A_or_B` is only a
constructor destructor for an already supplied `Node63Stage`. It does not
construct that stage from `InitialResidual` and it does not prove the official
statement. Migration therefore has two separate gates:

1. reproduce the normalized Node63-stage destructor after Nodes61, 62, 64,
   and 63 are migrated; and
2. prove a root-derived executor theorem that constructs the stage through the
   manuscript DAG.

The first gate is type parity only and remains `migrated_open`. The Type A/B
reduction is not reproduced until the second theorem kernel-checks from the
minimal root without the legacy `largeEnoughTail` premise.

### 17.7 Per-wave exit gate

- Every node in the wave has a direct new source facade.
- Every direct facade has a fresh `.olean`.
- Every non-missing obligation has a compiled evidence step.
- Legacy and new status are shown separately.
- All closed nodes are parity-checked and checked against
  `original_erdos_64_proof.tex`.
- Open migrated nodes expose named residuals.
- The next frontier is computed from the original-authority topology: all
  direct parents closed.
- `migration-test` passes.

## 18. Phase 9: complete Graph ownership and reusable theorem migration

EG migration will reveal legacy graph modules that belong at different layers.
Move them according to semantics, not current file location.

### 18.1 Move to Core

Move or reimplement in Core anything stated only with finite types, ordered
families, labels, relations, response values, capacities, or ranks. Typical
examples:

- finite response comparison;
- same-interface response algebra;
- finite first failure;
- role-fibre overload;
- deterministic assignment;
- aggregate capacity;
- support-stratified rank when no graph operation appears; and
- generic finite peeling or packing.

Each move requires a non-graph fixture.

### 18.2 Keep in Graph

Graph owns declarations whose statements fundamentally mention:

- `SimpleGraph` adjacency;
- graph isomorphism;
- paths, walks, cycles, cliques, colorings, or minors;
- induced subgraphs;
- deletion or contraction;
- graph boundaries and gluing;
- graph degree preservation;
- graph target reflection; or
- graph occurrence/support semantics.

### 18.3 Keep in the EG application

The following never enter generic Hypostructure Graph:

- `P13` and thirteen-position codes;
- fixed power-of-two target arithmetic;
- quarter-credit curvature;
- fans, shoulders, and theorem-specific ports;
- Type A/Type B names;
- D1/D3/D4/D5/D7 clauses;
- hot/cold/germ/long-prefix/cold-skeleton branch names;
- theorem-specific surplus patterns; and
- paper node numbers.

Generic support, boundary, incidence, response, charge, and role concepts may
live lower; EG supplies the concrete meanings and constants.

### 18.4 Reusable graph theorem fixtures

Migrate or rebuild independent graph examples as pressure tests:

- greedy coloring;
- Mantel's theorem;
- an even-cycle or series-reduction example;
- minimum-degree cycle extraction;
- matching/packing; and
- boundaried replacement.

These examples must depend only on Hypostructure. They ensure the Graph API is
not merely a renamed EG implementation.

### 18.5 Graph completion gate

- All CT1-CT17 graph constructors needed by the API exist.
- Reusable graph theorems use public Core/Graph interfaces only.
- No EG identifier appears under `hypostructure/Hypostructure/Graph`.
- Graph has no route implementation outside Core/Routes.
- All graph targets transport through explicit isomorphism invariance.
- At least three independent graph applications build.

## 19. Phase 10: implement the PDE fast-track row by row

After the minimal PDE model is stable, implement the continuum fast-track from
`PDEs/10_continuous_extension.ipynb`. Every row consumes the propagated result
of the previous row. Closed classes enter the closed-class ledger before the
next invariant is evaluated.

### 19.1 Rows 1-4: registration

These are certification stages, not fake CT runs.

| Row | Implement | Required fixture |
|---|---|---|
| 1. Legal signature | Represented model, observable algebra, target interface | Finite scalar model and NS2D model register |
| 2. Generator/form | Closed form/generator capability and sector/decomposition laws | Finite matrix generator or explicit quadratic form |
| 3. Budget | Resource monoid and B1-B4 transcript | Natural budget and energy-like real budget |
| 4. Quotient defect | Framework-computed `L_X U - U L_Q` | Finite-dimensional quotient with known defect |

The author provides represented operators and laws. The framework computes the
derived transcript and appends it to the proof ledger.

### 19.2 Row 5: directed exhaustiveness

Implement the structural-gradient/closed-range profile using one focused,
counted CT15 to CT16 to Core class-closure executor. CT15 is only a finite
rank audit. Each of its two full-rank terminals reaches the analytic branch
through an explicit theorem producing a genuine positive Poincare gap for the
registered closed densely defined structural-gradient operator. A rank drop
only enables the independent compactification-code audit.

CT16 must reuse one counted support scan, count its closed-code computation
and equality comparison, rule out proper support for this row, and prove that
its exact/mismatch terminals agree with class-closure avoidance/visibility.
The class-closure family must separately satisfy `TargetComplete`; only then
does Core upgrade exhaustive avoidance to literal whole-quotient
`BoundaryZero`. Outcomes:

- positive structural gap with framework-derived closed range and orthogonal
  directed exhaustiveness;
- target-complete zero boundary quotient and framework-owned ledger
  propagation; or
- exact in-window target-visible boundary-defect residual with positive
  target capacity and nonzero certified target flux.

The last outcome does not reach the target at row 5. Realization/nonpolarity
remains a downstream certificate. A regularized ridge solve is never accepted
as exact closed range.

Validate first on a finite-dimensional linear operator before the NS2D
instance supplies any analytic closed-range theorem. The finite fixture tests
routing and ledger semantics; because finite-dimensional ranges are closed,
it is not evidence for a genuinely nonclosed continuum range.

### 19.3 Row 6: routing

Implement defect routing and harmonic residual classification through CT13 and
CT7:

- routable component with finite resistance;
- harmonic component already closed by the ledger; or
- nonroutable target-visible residual.

Use a finite orthogonal decomposition fixture and then a pressure-gauge toy.

### 19.4 Row 7: capacity

Implement affordable target capacity with CT14 and CT1:

- zero-capacity target exclusion enters the closed ledger; or
- positive-capacity target witness remains as the named reaching residual.

Test a finite network-style capacity before any continuum capacity theorem.

### 19.5 Row 8: committor/operator

Implement exact response comparison through CT3 and CT7. Track projection
error explicitly. Outcomes are response-complete quotient or approximation/
residual obstruction.

### 19.6 Row 9: scale reaching

Implement CT17 bounded scale arithmetic, CT12 scale/profile peeling, and CT11
budget localization. Outcomes:

- positive fixed-profile gap and finite-budget contradiction;
- zero-cost profile;
- moving-scale residual; or
- target-visible survivor.

The first fixture uses a finite list of scales. No uncountable scale search is
encoded as computation.

### 19.7 Row 10: SCRC and boundary repair

Implement finite classifier, cost localization, aggregate capacity, and target
validation through CT10, CT11, CT14, and CT1. Escaping classes are ledgered
before the in-window rigid/cost split. The complementary branch is the exact
in-window target-visible boundary-defect class.

### 19.8 Row 11: conservative carrier

Implement local witness aggregation and capacity comparison through CT5,
CT14, and CT11. The framework constructs the carrier remainder ledger and
reduced sign input. The application supplies only the carrier identity and
uniform remainder estimates.

### 19.9 Row 12: elliptic constraint tail

Implement:

- local elliptic inverse;
- homogeneous tail on the core;
- dyadic exterior schedule;
- low-mode/gauge map;
- tail aggregation;
- cokernel rank; and
- primary/fallback routing.

Use CT3, CT14, CT15, and CT13. The framework constructs local/tail objects,
dyadic aggregate, quotient, and route. For Navier--Stokes this becomes the
localized Calderon--Zygmund pressure plus harmonic tail, but those analytic
estimates remain explicit model certificates.

### 19.10 Row 13: ledger propagation

Implement the Core propagation executor and no-rechecking theorem in the real
PDE layer. Verify:

- boundary classes close first;
- tail classes close second;
- later flux forms descend to the twice-reduced space; and
- no later row imports or re-proves an earlier estimate.

### 19.11 Row 14: flux sign

Implement the sign/gap normal form with CT10, CT11, and CT1:

- strict radius below one closes/registers the estimate;
- radius above one emits a feeding profile;
- equality emits the exact compactified equality residual; and
- a zero lower gap emits a minimizing-sequence residual.

### 19.12 Row 15: borderline equality

Implement saturation aggregation and whole-support classification through
CT14, CT16, and CT10. A zero saturation quotient is propagated. A nonzero
quotient is a target-visible saturated class.

### 19.13 Row 16: rigidity/separator

Implement CT7 response distinction, CT16 equality-support audit, and CT1
closure. Accepted inputs are represented Liouville, Pohozaev, Noether,
modulation, virial, monotonicity, or positive-separator theorems. A nonzero
equality quotient remains an explicit residual.

### 19.14 Rows 17 and 17b

Row 17 lifts the same profiles pathwise or in expectation, with explicit
martingale-control residuals. Row 17b implements conditional-expectation gauge
projection, fluctuation resistance, rank/capacity accounting, and the exact
positive-capacity fluctuation residual.

These rows are optional for the first deterministic NS2D model but must exist
before the PDE layer is declared complete.

### 19.15 Row 18: affordable target completeness

Implement CT16 final quotient audit and CT1 target closure. The executor checks:

- escaping classes are in the residual zero-target ledger;
- zero-capacity and zero-flux in-window classes are closed;
- every closed class has a named non-reaching certificate;
- every nonzero final class is one of the registered target-reaching
  alternatives; and
- no unlisted in-window target-visible quotient remains.

Only this executor may turn a completed fast-track sheet into the final local
target. Pointwise local-to-global assembly then uses the PDE atlas and covering
profile.

### 19.16 PDE row gate

A row is complete only when:

- the axiom-free toy fixture passes;
- the complementary residual is tested;
- prior closed ledgers are consumed rather than reconstructed;
- the NS2D model either instantiates the row or records a precise missing
  analytic contract;
- work/execution semantics are appropriate to finite residual-owned data;
- no continuum is silently enumerated; and
- the row's `#print axioms` output is recorded.

### 19.17 PDE completion gate

- Rows 1-18 and 17b have public executors and fixtures.
- The three fast-track normal forms are implemented.
- Coordinate changes, local/tail assembly, quotienting, extraction, and
  routing are framework-owned.
- The NS2D model reaches every row for which its analytic inputs are available.
- Missing analytic theorems are explicit local contracts, not framework gaps.
- Generic PDE contains no EG or graph identifier.

## 20. Phase 11: catalogs, kernel evidence, and web dual-run

The web layer must show migration truth without overwriting legacy truth.

### 20.1 Separate example IDs

Use distinct IDs during migration:

```text
erdos-64
hypostructure-erdos-64
hypostructure-pde-fixtures
hypostructure-ns2d
```

The legacy EG page remains unchanged. A comparison view may align node IDs,
but it never merges status fields.

### 20.2 Hypostructure node status

For a new EG node:

- **green:** direct `HypostructureErdos64EG/NodeX.lean`, fresh `.olean`, all
  required obligations proved, and compiled evidence present;
- **yellow:** direct file exists but is not fresh/kernel-checked or has a
  partial mathematical obligation;
- **white:** no direct file;
- **orange:** no direct file and every direct parent is green in the immutable
  topology from `original_erdos_64_proof.tex`.

Parity status is displayed separately and never determines color.

### 20.3 Evidence integrity

Every non-missing obligation must reference a compiled proof step. The renderer
rejects:

- non-missing obligations with no evidence;
- evidence declarations absent from the compiled export;
- stale source hashes;
- a node claimed by an aggregate theorem without a direct facade;
- a fresh legacy `.olean` used as new-framework evidence; and
- a topology edge whose source or target is absent from the manifest.

### 20.4 Authority-owned topology and compiled descriptors

For EG, the complete Node 1-157 topology is owned by
`original_erdos_64_proof.tex` and committed explicitly in the migration
updater. A compiled example descriptor mirrors, but does not discover, these
fields:

- node IDs;
- edges;
- original-paper status;
- internal-helper distinction;
- direct source path;
- obligation IDs; and
- frontier policy.

The renderer validates this descriptor against the authoritative migration
matrix before using it. Legacy imports and source inventory can populate source
paths and evidence bindings only. Source-only Nodes 158-164 use the separate
supplemental inventory and never enter the EG descriptor's paper frontier or
completeness calculation. Other applications may provide their own explicit
authority-owned descriptors so the renderer can also support PDE rows and
future proof programs.

### 20.5 Migration dashboard

The comparison view should expose:

- legacy kernel status;
- new kernel status;
- parity status;
- mathematical status;
- required framework features;
- blocking residual;
- source links; and
- trust-boundary delta.

Do not use one color to encode all these dimensions.

### 20.6 Tooling gate

- Web backend loads with no stale-hash override.
- Legacy and Hypostructure catalogs validate independently.
- Comparison data validates against a dedicated migration schema.
- Direct-file status tests cover green/yellow/white/orange.
- The historical `erdos-64` artifact remains byte-stable unless intentionally
  refreshed.

## 21. Phase 12: final cutover

Cutover is a separate phase, not the last node-migration commit.

### 21.1 Entry conditions

All of the following must hold:

- Core API matches `DOMAIN_INDEPENDENT_CORE.md`;
- Graph API matches `GRAPH_LAYER_API.md`;
- PDE API matches `PDE_LAYER_API.md`;
- CT1-CT17 and all required routes are complete;
- every migrated EG node is classified closed or explicit frontier;
- every claimed green node has direct kernel evidence;
- reusable graph examples pass;
- PDE fixtures and NS2D registration pass;
- all generated artifacts are fresh;
- all trust audits pass;
- the import firewall passes; and
- `migration-test` passes from a clean checkout.

### 21.2 Cutover sequence

1. Freeze legacy development except critical correctness fixes.
2. Regenerate a final old/new comparison report.
3. Switch default Make targets to Hypostructure.
4. Switch example dependencies from `../../lean` to
   `../../hypostructure` where the examples have been migrated.
5. Promote Hypostructure catalogs to canonical generated paths.
6. Switch the web default example from the legacy EG implementation to the
   Hypostructure EG implementation.
7. Run the complete release gate.
8. Delete legacy `StructuralExhaustion` sources and migrated legacy example
   sources in one dedicated cleanup change.
9. Delete parity-only packages and test bridges.
10. Remove old catalog schemas, render paths, allowlists, and Make targets.
11. Search the repository for remaining production imports and names.
12. Regenerate all catalogs, diagrams, hashes, and kernel manifests.
13. Run the release gate again from a clean checkout.
14. Tag `hypostructure-v1.0.0` only after the second clean run.

### 21.3 Required absence checks

Final CI rejects:

- `import StructuralExhaustion`;
- `import Erdos64EG` in new production code;
- `Future`, `Legacy`, or compatibility namespaces;
- old package path dependencies;
- custom handoff declarations;
- stale legacy generated artifacts;
- unallowlisted axioms;
- application route constructors; and
- direct node status not backed by a fresh `.olean`.

### 21.4 No in-tree archive

Do not move old Lean files to `archive/` inside the production import tree.
The baseline tag and Git history preserve them. Keeping compilable old modules
would weaken the import firewall and invite accidental fallback.

## 22. Standard implementation workflow

Use this workflow for every Core feature, domain capability, CT, route, PDE
row, and EG node.

### 22.1 Before coding

- Identify the exact specification section.
- Identify the first graph and PDE/neutral consumers.
- Read the corresponding legacy implementation only as evidence and
  inspiration.
- Record all legacy assumptions and transitive axioms.
- State author inputs and framework outputs.
- Enumerate every residual branch.
- Decide the owner using the vocabulary test.
- Add or update the feature/node/row matrix.

### 22.2 During coding

- Add the smallest semantic primitives first.
- Derive searches, outputs, and routes in framework code.
- Keep production imports one-directional.
- Add the negative/complementary branch before declaring the positive branch
  complete.
- Add work accounting with the executor.
- Add metadata with the public declaration.
- Keep theorem-specific constants outside generic modules.
- Do not introduce an adapter merely to make old and new types match.

### 22.3 Focused verification

- Run the edited file directly with `lake env lean`.
- Run its immediate fixture.
- Inspect `#print axioms` for the public endpoint.
- Run the import linter.
- Confirm the node can retrieve a root and predecessor fact from the ledger.
- Confirm every route returns the full target-labelled accumulated ledger.

### 22.4 Integration verification

- Build the Hypostructure package.
- Build the affected new application.
- Build the parity package.
- Rebuild the unchanged legacy target.
- Regenerate Hypostructure catalogs.
- Validate schemas and web evidence.
- Run the relevant Python/frontend tests.

### 22.5 Review questions

Every review answers explicitly:

1. What is the literal incoming residual?
2. What single new mathematical fact does this unit add?
3. Which inherited facts are ledger queries?
4. Who owns coordinate changes and assembly?
5. Who owns the decision and route?
6. What are all complementary residuals?
7. Does each residual have a consumer?
8. What closes each terminal?
9. Which axioms are in the transitive dependency cone?
10. What finite universe is scanned, and who supplied it?
11. What is the work bound?
12. What independent fixture prevents EG overfitting?
13. Does the PDE side expose a missing abstraction?
14. Is parity semantic rather than record-shape equality?
15. Is web status backed by a direct fresh source artifact?

## 23. Detailed acceptance checklists

### 23.1 Core feature checklist

- [ ] Name contains no domain vocabulary.
- [ ] Public inputs are irreducible primitives.
- [ ] Derived data is not an author field.
- [ ] All outcomes are typed.
- [ ] Full predecessor ledger is retained.
- [ ] Coordinate/state transport is framework-owned.
- [ ] Graph fixture passes.
- [ ] PDE or neutral fixture passes.
- [ ] Negative fixture passes.
- [ ] Work bound is stated.
- [ ] Metadata is exported.
- [ ] No unallowlisted axiom appears.

### 23.2 Graph capability checklist

- [ ] Uses Mathlib graph definitions directly.
- [ ] Finite schedule is explicit and deterministic.
- [ ] Isomorphism transport is proved.
- [ ] Target invariance is explicit.
- [ ] Boundary ownership is exact.
- [ ] Reconstruction is proved, not assumed.
- [ ] No EG constant or paper branch appears.
- [ ] Core performs route and ledger updates.
- [ ] At least one non-EG graph fixture passes.

### 23.3 PDE capability checklist

- [ ] Window and topology are explicit.
- [ ] Representative/gauge status is explicit.
- [ ] Coordinate realization is explicit.
- [ ] Equation stability is proved at the declared regularity.
- [ ] Local/tail reconstruction is exact.
- [ ] Retained obstruction transport is explicit.
- [ ] No ambient continuum is enumerated.
- [ ] Missing analytic input is a named contract/residual.
- [ ] Closed ledgers propagate before later checks.
- [ ] A toy fixture exercises the capability axiom-free.

### 23.4 CT checklist

- [ ] Spec and Capability contain only primitive semantics.
- [ ] State is predecessor-indexed.
- [ ] Search is deterministic.
- [ ] Every branch is represented.
- [ ] Soundness is proved.
- [ ] Totality is proved.
- [ ] Exhaustiveness is proved.
- [ ] Trace validity is proved.
- [ ] Work is bounded.
- [ ] Public executor returns an accumulated stage.
- [ ] Metadata has no hidden manual obligation.
- [ ] Domain constructors do not duplicate execution.

### 23.5 Route checklist

- [ ] Source residual kind is exact.
- [ ] Source ledger is complete.
- [ ] Semantic discovery is a capability.
- [ ] Target input is framework-constructed.
- [ ] Target public executor is used.
- [ ] Disabled route is a typed residual.
- [ ] Predecessor is retained.
- [ ] Provenance is recorded.
- [ ] Full target ledger is returned.
- [ ] Source facts remain queryable after routing.

### 23.6 EG node checklist

- [ ] Direct paper predecessors match the manifest.
- [ ] New file imports only the direct predecessor/join and public APIs.
- [ ] Node adds one paper-local responsibility.
- [ ] P13/fan/port data stays application-local.
- [ ] No inherited output is copied.
- [ ] No branch is caller-selected.
- [ ] All residuals match paper edges.
- [ ] Legacy parity is proved or a deliberate repair is documented.
- [ ] Manuscript closure is independently audited.
- [ ] Direct `.olean` is fresh.
- [ ] Evidence step compiles.
- [ ] Web status is correct.

### 23.7 PDE fast-track row checklist

- [ ] Exact predecessor propagated quotient is input.
- [ ] Row capability matches the notebook.
- [ ] CT chain is framework-owned.
- [ ] Success invariant is represented.
- [ ] Complementary target-reaching residual is represented.
- [ ] Prior closed classes are not re-estimated.
- [ ] Equivalence with explicit calculation is stated/proved at the interface.
- [ ] Axiom-free toy fixture passes.
- [ ] NS2D status is explicit.

## 24. Performance and computation policy

The rewrite must preserve proof auditability and practical build times.

### 24.1 Finite search policy

- Scan only explicit residual-owned finite families.
- Use symbolic coverage for infinite outside-context types.
- Cache expensive fixed finite certificates behind stable module boundaries.
- Keep proof-relevant decisions in Lean; external generators may produce data
  only when Lean rechecks a complete certificate.
- Record exact visible checks and an asymptotic bound.
- Avoid powerset, graph-family, context-family, or Boolean-cube enumeration
  when the manuscript supplies a smaller local universe.

### 24.2 Build policy

- Focused files should compile independently.
- Large fixed certificates get isolated modules so downstream node edits reuse
  `.olean` files.
- Root barrels do not import tests or expensive optional examples.
- Parallel builds are allowed only after dependency correctness is established;
  serialized focused checks remain available for debugging.

### 24.3 Regression thresholds

For each migrated executor, record:

- old visible check count/bound;
- new visible check count/bound;
- old and new memory-relevant universe sizes; and
- explanation for any regression.

An asymptotic regression blocks migration unless the old bound was unsound or
the new behavior is required by a corrected manuscript contract.

## 25. Trust and axiom audit plan

### 25.1 Core trust target

The transitive axiom set of every Core, CT, Route, generic Graph, and generic
PDE public theorem is empty apart from Lean/Mathlib foundations reported by
`#print axioms` such as quotient soundness or classical choice. No authored
axiom is permitted.

### 25.2 EG trust target

The final EG proof may use only the exact allowlisted external graph theorem(s)
the mathematical strategy treats as black boxes. The HSS declaration, if
retained, is ported with the same exact statement and source record. No node
may widen it.

### 25.3 PDE trust target

PDE imports are itemized by theorem, source, assumptions, and first consumer.
The kernel manifest reports them separately from framework axioms. A theorem
about local compactness, pressure decomposition, epsilon regularity, or
Liouville rigidity is allowed only at the local contract boundary. No final
regularity conclusion is imported.

### 25.4 Trust delta report

The parity artifact reports for each migrated endpoint:

- legacy authored axioms;
- Hypostructure authored axioms;
- added imports;
- removed imports; and
- whether the trust boundary narrowed, stayed equal, or widened.

Any widening blocks merge until explicitly reviewed against the source paper.

## 26. Risk register

| Risk | Failure mode | Mitigation |
|---|---|---|
| Stale baseline | New behavior is compared with outdated generated claims | Clean Phase 0 build and hashed snapshot |
| Record-shape parity | Test passes only because old data was copied | Compare normalized mathematical observations |
| EG overfitting | Core acquires P13/fan-specific concepts | Import firewall, vocabulary test, PDE/neutral fixture |
| PDE under-specification | `Solution` hides regularity or gauge assumptions | Explicit represented equation and import contracts |
| Fake closure | A route or parity theorem is treated as terminal | Framework closure checker and separate math status |
| Hidden assumptions | Legacy conditional payload is copied | Assumption inventory and residual promotion |
| Custom handoff relapse | Application constructs a downstream input | No public handoff API; add generic executor |
| Ledger loss | Focused branch drops sibling or root facts | Retrieval tests after every decision/route |
| Coordinate drift | Recenter/rescale/gauge is recomputed manually | Core path executor and transport laws |
| Gluing mismatch | Replacement graph only looks isomorphic | Explicit semantic equivalence and reconstruction proof |
| Infinite search | Continuum/context class is treated as finite | Residual-owned finite family or symbolic coverage theorem |
| Trust widening | PDE/graph black box grows into final theorem | Exact external allowlist and trust delta |
| Build explosion | Every node recompiles fixed finite certificates | Stable certificate modules and focused builds |
| Web false green | Aggregate/stale artifact marks a node proved | Direct source plus fresh `.olean` plus evidence |
| Numeric node order | A node migrates before a real predecessor | Compiled manuscript DAG and join typing |
| Dual-system confusion | Old and new generated artifacts overwrite each other | Separate package, IDs, catalogs, and web views |
| Premature cleanup | Legacy reference disappears before parity | Cutover-only deletion |

## 27. Milestones

### M0: Baseline frozen

- Legacy test suite passes.
- Baseline artifacts and topology are committed.

### M1: Hypostructure package alive

- Independent package and import firewall pass.
- Legacy behavior is unaffected.

### M2: Shared Core vertical slice

- Problem, residual ledger, decisions, coordinates, assembly, budgets, and
  closure run on graph and PDE toys.

### M3: Both domains registered

- New EG problem definition and official-statement parity pass.
- NS2D model and zero-solution fixtures pass.

### M4: First CT chain

- CT1-CT3 and first routes execute in both framework fixtures and EG nodes.

### M5: Early EG prefix

- Nodes 1-18 migrate with parity and manuscript closure.
- CT10/CT12 and graph gluing are stable.

### M6: First PDE fast-track prefix

- Rows 1-8 execute on axiom-free finite/analytic toys.
- NS2D registers every available capability honestly.

### M7: Full CT framework

- CT1-CT17, current route families, metadata, and work bounds pass.

### M8: Full EG migration

- Every supported node has a direct Hypostructure facade and correct status.
- Every unresolved paper obligation is an explicit frontier residual.

### M9: Full PDE framework

- Rows 1-18 and 17b, closed-ledger propagation, and local-to-global assembly
  pass their fixtures.

### M10: Tooling cutover

- Canonical catalog, kernel manifest, schemas, and web use Hypostructure.

### M11: Legacy removal

- Old implementation and parity harness are deleted.
- Clean release gate passes.
- `hypostructure-v1.0.0` is tagged.

## 28. Definition of done

### 28.1 Core complete

Core is complete when it supports, with no domain imports:

- external targets and optional progress;
- contexts and one accumulated residual ledger;
- typed decisions, joins, and closures;
- semantic equivalence and target invariance;
- framework-owned coordinate paths;
- dependent atom/context assembly;
- finite response algebra;
- abstract closed-class ledgers and quotients;
- compact extraction with retained obstruction;
- mathematical and verifier budgets;
- CT execution and full-ledger routing; and
- canonical metadata and trust auditing.

### 28.2 Graph complete

Graph is complete when:

- packed finite graphs and deterministic scans are stable;
- graph isomorphism, coordinates, restriction, deletion, contraction,
  boundaries, and gluing are proved;
- every CT has the required graph constructor;
- generic graph theorem examples pass;
- EG-specific vocabulary is absent; and
- all routing is Core-owned.

### 28.3 PDE complete

PDE is complete when:

- local models, atlases, equations, observables, gauges, coordinates,
  local/tail assembly, compactness, budgets, and target interfaces are stable;
- every fast-track row has an executor and complementary residual;
- closed-class propagation prevents rechecking;
- finite/analytic toy fixtures are axiom-free;
- NS2D is faithfully represented; and
- missing analytic mathematics is visible at explicit theorem contracts.

### 28.4 EG migration complete

The EG migration is complete when every paper node in scope is either:

- directly kernel-checked and closed through Hypostructure; or
- directly kernel-checked as an explicit active residual with a named missing
  mathematical producer.

No aggregate theorem, old `.olean`, copied output, or parity result can satisfy
this condition.

### 28.5 Repository migration complete

The repository migration is complete when:

- Hypostructure is the only production framework;
- all canonical examples depend on it;
- catalogs and web evidence are Hypostructure-native;
- legacy and parity packages are absent;
- all source, kernel, schema, generation, Python, and frontend tests pass from
  a clean checkout; and
- the final trust manifest contains only the explicitly approved local
  external theorems.

## 29. First implementation sequence

The first concrete implementation work should follow this exact order:

1. Freeze and commit the baseline manifest.
2. Create the independent `hypostructure/` Lake package.
3. Add the import/admission firewall and Make targets.
4. Implement `Core.Problem`, external targets, optional `Progress`, and
   contexts.
5. Implement the proof ledger, typed queries, decisions, focused continuation,
   and joins.
6. Implement semantic equivalence and target invariance.
7. Implement coordinate paths and transport.
8. Implement dependent atom/context assembly.
9. Implement resource/work budgets and generic closure.
10. Implement the packed finite Graph object, isomorphism, restriction, and
    direct cycle target.
11. Define the new EG official statement, target algebra, problem, and initial
    residual; prove parity with the legacy problem.
12. Implement the minimal PDE model, additive local/tail fixture, gauge toy,
    and coordinate fixtures.
13. Define the NS2D model and prove zero-solution/coordinate/gauge fixtures.
14. Implement CT1 completely and migrate EG nodes 1-3 as the first vertical
    slice.
15. Implement CT2 plus CT1-to-CT2 and migrate nodes 4-10.
16. Implement CT3 plus Graph gluing and migrate nodes 11-14.
17. Port the exact HSS external theorem contract and migrate nodes 15-16.
18. Implement CT12 and CT10; migrate nodes 17-18.
19. Continue by the topology of `original_erdos_64_proof.tex`, invoking the
    framework-gap protocol for every missing generic operation.
20. In parallel after each CT wave, implement the corresponding PDE toy and
    fast-track row so Core remains genuinely cross-domain.

This order produces useful end-to-end proof slices early, keeps the old EG
application available as a regression oracle, and continuously tests that the
new Core serves both finite graph exhaustion and local/global PDE analysis.
