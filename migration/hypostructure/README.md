# Hypostructure Migration Records

This directory is the machine-readable execution ledger for
`HYPOSTRUCTURE_MIGRATION_GUIDE.md`. The records separate source inventory,
kernel evidence, parity, mathematical closure, and publication status.

## Authority by Concern

### EG authority preflight

For every Erdős--Gyárfás Problem 64 task, read
`original_erdos_64_proof.tex` **FIRST**, before any API/process document,
migration row, generated view, living proof, or legacy Lean source. It is the
immutable sole authority for EG mathematics, strategy, node identity and
responsibility, and DAG topology. Freeze the exact quantified node contract,
branch alternatives, and exact incoming/outgoing DAG edges from that file.

Only after that contract and those edges are frozen may the matching
kernel-checked legacy `NodeX.lean` be read, and then only as implementation and
parity evidence. `proofs/erdos_64_eg/erdos_64_proof.tex` is a living,
non-binding editorial cross-check; it cannot repair, supplement, weaken,
strengthen, or redirect the original contract or edges. Any discrepancy blocks
the task: record it and stop rather than reconciling the sources or silently
changing the obligation. Never edit `original_erdos_64_proof.tex` during
ordinary migration work.

### Framework ownership and status

After the EG preflight, `HYPOSTRUCTURE_MIGRATION_GUIDE.md` governs migration
process and status semantics. `DOMAIN_INDEPENDENT_CORE.md`,
`GRAPH_LAYER_API.md`, and `PDE_LAYER_API.md` govern framework ownership and
required public capabilities. These API/process documents never outrank or
reinterpret `original_erdos_64_proof.tex` on EG mathematics, node
responsibility, or DAG topology.

Direct Hypostructure Lean source defines current imports and declarations;
fresh `.olean` files provide kernel evidence only. Migration matrices record
reviewed inventory and status. Generated catalogs and web data are evidence
outputs only: they never create a theorem, node, edge, status, or closure claim.

`source-authority.json` pins the immutable original manuscript by SHA-256 and
byte size and records the non-authority roles of the living proof and legacy
Lean. Any digest change is a failed migration gate unless an explicit source
correction has first been approved; ordinary migration work must never update
the manifest to accommodate an unapproved edit.

`eg-original-node-anchors.json` is an exact, generated locator for the 157
node commands in the original proof-dependency diagram. It stores source byte
and line slices and their hashes, but its scope is deliberately
`diagram_anchor_only`: it does not certify a node's hypotheses, quantifiers,
outcomes, cited definitions, or full contract. Use it to open the right place,
then read and freeze the complete requirement from
`original_erdos_64_proof.tex` itself before opening any legacy Lean file.
Verify the locator against the pinned original with:

```bash
python3 tools/extract_eg_original_node_anchors.py --root . --check
```

## Ledgers

- `api-feature-matrix.csv` tracks the complete reviewed Core, CT, Routes,
  Graph, and PDE feature inventory. Existing bootstrap features retain their observed
  build status; unimplemented contracts remain `planned`.
- `eg-node-matrix.csv` contains exactly the 157 nodes of
  `original_erdos_64_proof.tex`. Its predecessor field is generated from one
  complete, explicit original-derived map; no Lean import may alter it. Nodes
  65-144 lack direct legacy facades, so their declaration bindings remain
  explicit blockers.
- `supplemental-legacy-evidence.csv` records source-only legacy Nodes 158-164 as
  implementation/parity observations. They are not paper nodes and are
  excluded from the EG DAG, frontier, migration status, and completeness.
- `pde-row-matrix.csv` has rows 1-18 plus 17b from
  `PDEs/10_continuous_extension.ipynb` and `PDE_LAYER_API.md`.

Numeric node order is not topological order. In particular, the matrix records
cross-panel joins and feedback edges such as 66 to 65, 102 to 89, and the
original Node 59 split to Nodes 60 and 61 without rewriting them into a linear
chain.

`parity_status` and `math_status` are independent. A fresh legacy object file
does not make a Hypostructure node migrated, mathematically closed, or
publishable.

PDE rows use `not_checked`/`kernel_checked` for local kernel evidence and
`not_checked`/`fixture_checked`/`integration_checked` for progressively wider
execution evidence. Registration rows 1-4 may be fixture-checked before any
analytic Navier--Stokes capability is claimed for later rows.

## Refresh Discipline

The current source refresher can be run with:

```bash
python3 tools/update_hypostructure_migration_records.py --root .
```

For a topology/evidence-only refresh that leaves the API and PDE ledgers
untouched, run:

```bash
python3 tools/update_hypostructure_migration_records.py --root . --only eg
```

Its built-in `FEATURES` list covers the bootstrap API, all CTs, the complete
legacy route registry, and the additional EG/PDE route requirements. It also
preserves reviewed rows not yet source-derived through a key-preserving merge.
For EG nodes it derives only the observable status floor: absent source is
`inventoried`, present source without a fresh object is `scaffolded`, and a
fresh object is `typechecked`. Reviewed higher states are retained only while
that fresh kernel basis remains present; editing a node therefore invalidates
unsupported parity and migration claims automatically.
The EG refresh takes every predecessor of Nodes 1-157 from the complete map
reconstructed from `original_erdos_64_proof.tex`, including cross-panel
continuations, joins, and feedback edges. Direct `Node*.lean` imports are never
merged into that topology. Imports from source-only Nodes 158-164 are recorded
only in `supplemental-legacy-evidence.csv`. After any refresh, rerun the focused
tests to verify headers, key uniqueness, exact paper-node coverage, authoritative
edges, supplemental exclusion, and status vocabularies.

## Baseline

No parity baseline is frozen from the current dirty worktree. Instantiate
`baseline/manifest.template.json` only from a named clean commit after the
ordered legacy build, generation, kernel, validation, web, and test commands in
the guide succeed. Record hashes and freshness as observed values; do not infer
missing evidence from stale generated output.

## Trust Firewall

Run the standalone production check with:

```bash
python3 tools/check_hypostructure_imports.py --root .
```

The checker:

- scans the Hypostructure framework and new EG/PDE production packages while
  excluding the parity package;
- permits only Mathlib, Hypostructure, and the owning application import roots;
- rejects Core, CT, Routes, Graph, PDE, application, and reverse-legacy import
  inversions;
- rejects legacy, generated, parity, direct-route, compatibility, handoff,
  `Legacy`, and `Future` dependencies or declaration names;
- rejects authored `sorry`, `admit`, `unsafe`, plural axiom commands, constants,
  and unallowlisted axioms; and
- admits singular external axioms only by exact source path and local
  declaration name in `trust-allowlist.json`, failing on duplicate or stale
  entries.

The checked-in allowlist is intentionally empty. Additions require a reviewed
local theorem contract and a decision record; final theorem, route-closure, and
target-completeness assumptions are not admissible.

## Decisions

Use `decisions/0000-template.md` for API or trust-boundary changes. Each record
must identify owner inputs, framework outputs, all residual branches, both
Graph and PDE or neutral fixtures, compatibility impact, and baseline impact.
