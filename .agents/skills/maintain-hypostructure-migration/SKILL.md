---
name: maintain-hypostructure-migration
description: "Maintain the Structural Exhaustion-to-Hypostructure migration as an auditable dual-run program. Use when freezing or explicitly refreshing the legacy baseline, updating API/EG/PDE migration matrices, recording ownership or trust ADRs, checking semantic parity, enforcing the production import and axiom allowlists, reconciling direct source/`.olean` evidence, publishing separate old/new status, or executing the final cutover and removal gates."
---

# Maintain the Hypostructure Migration

Maintain evidence, not appearances. Keep source inventory, kernel freshness, semantic parity, mathematical closure, work, trust, integration, publication, and cutover as separate judgments.

## Follow the authority order

Resolve conflicts in this order:

1. `HYPOSTRUCTURE_MIGRATION_GUIDE.md` for process and status semantics.
2. `DOMAIN_INDEPENDENT_CORE.md`, `GRAPH_LAYER_API.md`, and `PDE_LAYER_API.md` for required ownership and public capabilities.
3. The target manuscript/notebook for topology and mathematical responsibility.
4. Direct Lean source for declarations/imports and fresh direct `.olean` files for kernel evidence.
5. Migration matrices for reviewed inventory/status.
6. Generated catalogs and web data as derived outputs only.

Legacy code is a frozen parity oracle until cutover, never a production dependency or API adapter. Only `examples/hypostructure_parity` may import both systems.

Maintain the three committed ledgers directly: `migration/hypostructure/api-feature-matrix.csv`, `migration/hypostructure/eg-node-matrix.csv`, and `migration/hypostructure/pde-row-matrix.csv`.

## Freeze the baseline before claiming parity

Read `migration/hypostructure/baseline/README.md`. If no `manifest.json` exists, report that no parity baseline is frozen; do not silently use the dirty worktree or stale generated output.

Freeze only from a named clean commit:

1. Record commit, tag, date, Lean toolchain, Mathlib revision, Python inputs, Node lock hash, and trust allowlist.
2. Run the ordered legacy gate without stale-hash overrides:

   ```bash
   make framework-build
   make erdos-example-build
   make generate
   make kernel
   make validate
   make web-test
   make test
   ```

3. Instantiate the baseline manifest and record observed artifact hashes, direct node source hashes, direct `.olean` freshness, public export declarations, trusted axioms, topology, partial obligations, and work bounds.
4. Verify generated data agrees with source before committing the snapshot.

Never freeze from uncommitted proof work. Commit intended legacy corrections first as legacy work, rerun the complete gate, then freeze.

## Control baseline refreshes with ADRs

Treat a baseline refresh as a compatibility change, not routine regeneration. Before refreshing:

1. create the next numbered record from `migration/hypostructure/decisions/0000-template.md`;
2. name old/new baseline commits and the reason behavior changed;
3. list affected API/node/PDE rows, parity expectations, work bounds, artifacts, and trust delta;
4. rerun the full clean baseline gate; and
5. replace hashes only with observed fresh outputs.

Do not refresh merely to make a parity failure disappear. Preserve old evidence and explain every normalized behavior change.

## Refresh the migration ledgers safely

Before running the source refresher, inspect `git status`, the current matrix diffs, and any reviewed statuses. Then run:

```bash
python3 tools/update_hypostructure_migration_records.py --root .
```

Inspect all three CSV diffs. The tool:

- updates source-derived API status from module/source and `.olean` freshness;
- preserves reviewed feature rows by key;
- refreshes EG direct predecessors from source plus the manuscript-only topology table;
- demotes reviewed EG states when their direct kernel basis becomes stale/missing; and
- preserves reviewed parity/math/work fields rather than proving them.

After every refresh, validate headers, unique keys, CT1-CT17 coverage, node coverage/topology, allowed vocabularies, and PDE rows including 17b. Never hand-promote a field from a neighboring field.

Use these state meanings exactly:

- API: `planned` -> `specified` -> `implemented` -> `kernel_checked` -> `integration_checked` -> `cutover`.
- EG migration: `inventoried` -> `scaffolded` -> `typechecked` -> `parity_checked` -> `migrated_open`/`migrated_closed` -> `published` -> `cutover`.
- Only `migrated_closed` is eligible for green mathematical status.
- PDE kernel and integration statuses remain separate.

## Record architecture and trust decisions

Create an ADR whenever one of the three API specifications changes, ownership changes, a reusable route/capability is added, an authored external theorem is requested, or the baseline refreshes. Record:

- missing use case and correct owner;
- primitive author inputs and framework-generated outputs;
- all complementary residuals and consumers;
- Graph plus PDE/neutral both-sides fixtures;
- work, compatibility, baseline, parity, and trust impact; and
- linked matrix rows and executable evidence.

An ADR is not implementation evidence. Leave matrix status unchanged until source, fixtures, and checks justify promotion. Never resolve compatibility with an alias, adapter, custom handoff, or production legacy import.

## Maintain semantic parity

Define parity only in `examples/hypostructure_parity`. Compare normalized paper-visible behavior: official inputs, baseline/target meaning, branch partitions in both directions, terminal/residual predicates, public facts, predecessor retention, work, and trust.

Use explicit relations between old/new representations; do not expose production conversion functions. Golden fixtures may compare deterministic tags/codes, but general parity requires theorems. Record manuscript-correct differences rather than reproducing unsupported legacy assumptions. Parity never establishes mathematical closure.

## Enforce the trust and import firewall

Run:

```bash
python3 tools/check_hypostructure_imports.py --root .
```

Keep `migration/hypostructure/trust-allowlist.json` exact, minimal, and free of stale entries. Any addition requires an ADR and a local Graph External or equation-specific PDE External contract naming its source, assumptions, locality/representation semantics, and first consumer.

Never allow an axiom for a final theorem, route closure, or target-completeness verdict. Audit public endpoints with `#print axioms` and report the old/new trust delta. A widening blocks migration until explicitly reviewed.

## Preserve the dual run

Until cutover:

- build old and new packages independently;
- keep legacy and Hypostructure example IDs, generated paths, schemas, and web views separate;
- display legacy kernel, new kernel, parity, mathematics, work, blocker, and trust delta independently;
- derive new node color only from its direct new source, fresh direct `.olean`, complete obligations, and compiled new evidence; and
- run `make migration-test` for a migration-wave merge.

Never overwrite the historical legacy artifact during an ordinary new-framework refresh. Never use one color or aggregate theorem to collapse migration state.

## Execute cutover only as a dedicated phase

Require all Core/Graph/PDE APIs, CT1-CT17, registered routes, target applications, fixtures, fresh catalogs, direct kernel evidence, trust audits, firewall, and clean `migration-test` to pass first. Require every in-scope EG node to be directly closed or an explicit named active frontier according to the approved release criterion.

Then follow the guide's ordered cutover: freeze legacy development, generate a final comparison, switch build/example/catalog/web defaults, run a clean release gate, remove legacy and parity packages in one dedicated cleanup, remove obsolete schemas/targets/allowlists, perform required absence searches, regenerate everything, rerun from a clean checkout, and tag only after the second clean gate.

Do not keep an in-tree archive or compatibility namespace. Git history and the baseline tag are the archive.

## Report maintenance results

Report baseline identity/freshness, matrix rows changed, source-derived versus reviewed fields, ADRs, direct kernel evidence, parity/math/work/trust deltas, firewall results, dual-run checks, blockers, and whether any cutover entry condition remains unmet. Never describe the migration as complete while a required field or clean gate is missing.
