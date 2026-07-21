# Hypostructure Migration Records

This directory is the machine-readable execution ledger for
`HYPOSTRUCTURE_MIGRATION_GUIDE.md`. The records separate source inventory,
kernel evidence, parity, mathematical closure, and publication status.

## Authority Order

Resolve conflicting evidence in this order:

1. `HYPOSTRUCTURE_MIGRATION_GUIDE.md` defines migration process and status.
2. `DOMAIN_INDEPENDENT_CORE.md`, `GRAPH_LAYER_API.md`, and
   `PDE_LAYER_API.md` define the required public capabilities and owners.
3. `original_erdos_64_proof.tex` is the immutable EG mathematical strategy,
   topology, and node-responsibility authority.
4. Kernel-checked legacy EG and Structural Exhaustion source provide the
   implementation and parity reference. The living manuscript is only a
   non-binding editorial cross-check.
5. Direct Hypostructure Lean source defines current imports and declarations;
   fresh `.olean` files provide kernel evidence only.
6. Generated catalogs and web data are evidence outputs. They never create a
   theorem, node, edge, status, or closure claim.

## Ledgers

- `api-feature-matrix.csv` tracks the complete reviewed Core, CT, Routes,
  Graph, and PDE feature inventory. Existing bootstrap features retain their observed
  build status; unimplemented contracts remain `planned`.
- `eg-node-matrix.csv` has the union of the 157 manuscript nodes and direct
  source-only nodes 158-164. Nodes 1-64 and 145-164 have direct legacy facade
  rows. Manuscript-only nodes 65-144 retain paper topology while their legacy
  declaration bindings remain explicit blockers.
- `pde-row-matrix.csv` has rows 1-18 plus 17b from
  `PDEs/10_continuous_extension.ipynb` and `PDE_LAYER_API.md`.

Numeric node order is not topological order. In particular, the matrix records
cross-panel joins and feedback edges such as 66 to 65, 102 to 89, and the
61-64 source import split without rewriting them into a linear chain.

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

Its built-in `FEATURES` list covers the bootstrap API, all CTs, the complete
legacy route registry, and the additional EG/PDE route requirements. It also
preserves reviewed rows not yet source-derived through a key-preserving merge.
For EG nodes it derives only the observable status floor: absent source is
`inventoried`, present source without a fresh object is `scaffolded`, and a
fresh object is `typechecked`. Reviewed higher states are retained only while
that fresh kernel basis remains present; editing a node therefore invalidates
unsupported parity and migration claims automatically.
The EG refresh merges direct
`Node*.lean` imports with an explicit original-manuscript topology table for nodes
65-144, including cross-panel continuations and feedback edges. After any
refresh, rerun the focused tests to verify headers, key uniqueness, node
coverage, paper edges, and status vocabularies.

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
