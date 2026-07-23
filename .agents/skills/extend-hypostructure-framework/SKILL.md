---
name: extend-hypostructure-framework
description: Add or improve reusable Hypostructure strategy capabilities in Core, Graph, or PDE. Use only after a proof strategy exposes a missing public operation, composition primitive, residual query, executable constructor, terminal consumer, work law, or domain adapter that cannot be expressed through the live strategy API.
---

# Extend the Hypostructure Framework

Prove the gap against live declarations before editing. The consumer must be a reusable strategy, never a manuscript node or application routing shim.

## Choose ownership

Put domain-neutral strategy contracts, execution, composition, ledgers, outputs, diagnostics, and budgets in Core. Put only graph semantics in Graph and represented analytic semantics in PDE.

## Use private backend playbooks

When a strategy requires lower-level machinery, load only the matching reference:

- `references/backend-ordered-exhaustion.md`
- `references/backend-response-classification.md`
- `references/backend-capacity-accounting.md`
- `references/backend-support-localization.md`
- `references/backend-target-avoidance.md`
- `references/backend-rank-budget.md`
- `references/backend-closed-code.md`
- `references/backend-routing.md`

These are framework-maintainer playbooks, not application skills.

## Complete the vertical slice

Implement an executable registered DAG-vertex constructor, exhaustive terminals, literal predecessor/ledger preservation, target and residual consumers, work evidence, and Graph/PDE-neutral Core tests. Then migrate the real consumer by adding that vertex to its `Dag.Blueprint`.

Reject problem constants, branch names, copied payloads, manual routes, placeholder outcomes, and APIs that merely package an unproved application theorem.
