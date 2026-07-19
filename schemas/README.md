# Automation-first JSON Schemas

The JSON Schema layer is a machine-readable projection of the canonical Lean
CT1--CT17 implementation. Lean owns mathematical meaning, graph topology,
typed transitions, capability boundaries, residual types, target execution,
and accumulated ledgers. Transition profiles expose whether residual-specific
semantic discovery is supplied by a problem adapter or by the target
capability. JSON Schema validates artifact shape and exact agreement with the
exported compiled environment; it does not prove the mathematics.

## Authority chain

```text
Lean Graph/Automation declarations
        -> StructuralExhaustion.Canonical.tactics,
           .transitionFamilies, and .transitionProfiles
        -> compiled-environment exporter
        -> generated/lean-machines.json
        -> generic authored schemas
        -> schemas/generated/* exact concrete schemas
```

The catalog records, for every tactic:

- its namespace and API version;
- minimal capability definitions, inferred instances, and framework-derived
  operations;
- Lean-owned semantic concepts for every required definition, including its
  compiled declaration, LaTeX mathematical notation, and plain explanation;
- every compiled node constructor and its ordinal;
- every typed `Graph.Edge` constructor and exact source/target indices;
- terminal constructors and mappings;
- per-node automation contracts;
- semantic residual-kind contracts;
- the registered CT transition families, their executable profiles, and their
  explicit framework/problem authoring boundaries.

Per-node automation contracts keep these categories separate:

- `authorInputs`: problem-specific definitions, operators, explicit Mathlib
  finite enumerators, or semantic bridges;
- `inferredInputs`: dependencies synthesized by typeclass search;
- `predecessorInputs`: the exact state fixed by the incoming typed edge;
- `derivedInputs`: reusable framework computation/search dependencies;
- `frameworkTheorems`: generic theorems used by the node;
- `transitiveDependencies`: the ordered concatenation of the preceding input
  categories;
- `generatedOutputs`: states, decisions, certificates, residuals, or audit
  objects constructed by the framework;
- `manualObligations`: obligations still left to a proof instance, expected to
  be empty in the canonical machines.

Terminal automation entries are synthesized by the compiled exporter from
incoming edge evidence and trace verification. They never become proof-author
inputs.

## Authored generic schemas

The files directly under `schemas/` are format contracts and may be edited when
the generic artifact model changes:

- `lean-machine-catalog.schema.json`: complete compiled catalog, including
  tactics, nodes, formal edge contracts, capabilities, residuals, transition
  families, executable transition profiles, and the provision taxonomy.
- `tactic-spec.schema.json`: one automation-first tactic projection.
- `node-spec.schema.json`: one predecessor-indexed node and formal edge
  boundary.
- `capability-spec.schema.json`: the minimal proof-instance capability
  manifest.
- `capability-concept.schema.json`: one documented capability requirement,
  anchored to its resolved compiled Lean declaration.
- `automation-profile.schema.json`: one node's author/framework provenance and
  generated-output contract.
- `provisioned-ref.schema.json`: a Lean reference paired with its provenance
  classification.
- `residual-kind.schema.json`: a semantic residual family and its inherited
  context.
- `transition-family.schema.json`: one source/target CT pair and its registered
  executable profile identifiers.
- `transition-profile.schema.json`: one Lean-owned residual-to-execution
  profile, including its target executable interface, constructor, full-ledger
  executor, semantic-discovery mode, and exact problem inputs.
- `machine-artifacts.schema.json`: exact sequential run records and tactic
  verification summaries.
- `verification-result.schema.json` and `kernel-verification.schema.json`:
  repository and Lean-kernel verification records.
- `lean-derived-manifest.schema.json` and
  `lean-derived-schema-index.schema.json`: generated artifact and concrete
  schema indexes.
- `example-catalog-raw.schema.json`, `example-detail.schema.json`, and
  `example-index.schema.json`: compiled worked-example workflows, hydrated Lean
  sources, and optional manuscript correspondence catalogs. Manuscript proof
  steps classify every displayed declaration by mathematical or verification
  role and carry validated LaTeX-label/diagram-node references. Optional
  `nodeObligations` are emitted by the Lean descriptor as stable property-level
  task ledgers; the renderer checks their proof-step evidence and green-node
  agreement before the frontend displays counts or colors.
- `erdos-proof-history.schema.json`: append-only engineering snapshots for the
  Erdős case study. It records artifact/manuscript hashes, Lean-owned node and
  obligation counts, explicit transition/binding reuse, and
  author/framework/external declaration ownership. It never derives proof
  status or estimates time saved.

All schemas use JSON Schema Draft 2020-12.

## Generated concrete schemas

`schemas/generated/index.json` is the canonical index of the specialized
schemas. The generator creates:

- `nodes/<node-id>.schema.json`: the exact compiled node value, automation
  contract, incoming edges, and outgoing edges;
- `tactics/CTN.schema.json`: the complete CT graph, capability, residual
  inventory, and API declarations;
- `residuals/<residual-kind>.schema.json`: one registered semantic residual;
- `transition-families/<family-id>.schema.json`: one registered CT-pair family;
- `transition-profiles/<profile-id>.schema.json`: one executable Lean
  transition profile;
- `runs/CTN.run.schema.json`: steps restricted to actual compiled edge
  constructors and terminals;
- `verifications/CTN.verification.schema.json`: exact graph counts and manual
  obligation count for a kernel summary.

These files are generated. Never edit them directly.

The number of concrete schemas is intentionally derived rather than documented
as a constant:

```bash
jq '{
  tactics: (.tactics | length),
  nodeSchemas: ([.tactics[].nodeSchemas[]] | length),
  residualSchemas: ([.tactics[].residualSchemas[]] | length),
  transitionFamilySchemas: (.transitionFamilies | length),
  transitionProfileSchemas: (.transitionProfiles | length),
  tacticLevelSchemas: ((.tactics | length) * 3)
}' schemas/generated/index.json
```

## Generate and validate

From the repository root, the supported workflows are:

```bash
make schemas   # build/export Lean, then regenerate concrete schemas
make erdos-proof-history  # append the current Erdős artifact if it is new
make generate  # schemas plus diagrams, indexes, manifests, and binding check
make validate  # validate the current catalog and generated schema tree
make verify    # regenerate first, then kernel-check and validate everything
make test      # make verify plus regression tests
```

If `generated/lean-machines.json` is already current, schema generation alone
is:

```bash
python3 tools/render_schemas.py \
  --catalog generated/lean-machines.json \
  --root .
```

Repository validation resolves cross-file `$ref` values offline, validates the
catalog and concrete schemas against Draft 2020-12, checks exact node/edge/
terminal projections, verifies capability coverage and provenance tags,
requires a unique non-orphaned concept for every general/profile definition,
rejects empty generated-output contracts or manual node obligations, checks
residual and transition-profile registration, exact family partitioning, and
enforces graph reachability and cycle decrease requirements.

```bash
python3 tools/validate_repository.py --root .
```

Kernel verification is separate and stronger: it builds Lean, compiles the
generated declaration binding check, rejects authored admissions, checks the
pinned Lean version, and compares a fresh temporary catalog export
byte-for-byte with the committed catalog.

```bash
python3 tools/verify_lean.py
```

## Validate an execution record

Run schemas restrict individual steps to compiled Lean edge constructors. The
run validator additionally checks sequential composition, start-node
agreement, and final terminal agreement:

```bash
python3 tools/validate_machine_run.py path/to/run.json
```

Use the tactic's generated schema under `schemas/generated/runs/` when
constructing a record. A valid JSON record is an auditable trace reference; the
evidence carried by the corresponding Lean `Graph.Path` remains the formal
proof.

## Changing the schema surface

1. Change CT semantics, topology, capability fields, node contracts, residuals,
   transition families, or profiles in Lean.
2. Change a generic schema only when the artifact format itself changes.
3. Run `make generate` to refresh every concrete projection.
4. Run `make verify` or `make test` before committing.

Do not hand-copy Lean declarations into JSON and do not add JSON-only nodes,
edges, residuals, transition families, or transition profiles. The validator
treats compiled Lean as the single source of truth.
