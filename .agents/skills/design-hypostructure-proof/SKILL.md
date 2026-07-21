---
name: design-hypostructure-proof
description: "Design a new Lean proof as a status-aware Hypostructure program over Core and CT1-CT17. Use when translating a manuscript argument into typed residuals, choosing Graph or PDE capabilities, selecting CTs and framework-owned routes, preserving one accumulated ledger, identifying author primitives with Core.Provision, estimating local work, or deciding that a missing operation must be added to Hypostructure before application proof work can continue."
---

# Design a Hypostructure Proof

Design against the public framework that exists now. Treat the API documents as the target architecture, the migration matrices as the reviewed status ledger, Lean source as declaration truth, and fresh `.olean` files as kernel evidence. Never call a planned signature as though it were implemented.

## Establish authority and availability

1. Work from `git rev-parse --show-toplevel`; inspect `git status --short` and preserve unrelated changes.
2. Read the exact theorem, manuscript proof, branch diagram, and direct predecessor obligations.
3. Use [`$understand-hypostructure-framework`](../understand-hypostructure-framework/SKILL.md), then read `HYPOSTRUCTURE_MIGRATION_GUIDE.md` and the relevant parts of `DOMAIN_INDEPENDENT_CORE.md`, `GRAPH_LAYER_API.md`, or `PDE_LAYER_API.md`.
4. Inspect the relevant rows in:
   - `migration/hypostructure/api-feature-matrix.csv`;
   - `migration/hypostructure/eg-node-matrix.csv` for the Erdős application; or
   - `migration/hypostructure/pde-row-matrix.csv` for the PDE fast track.
5. Confirm every intended declaration in `hypostructure/Hypostructure/**`, its public import path, and its build artifact. Do not infer availability from a proposed signature, a filename alone, the umbrella import, a legacy declaration, or a generated page.
6. Treat `planned` as unavailable. Treat `implemented` as source present but not yet kernel-backed. Before depending on either a newly implemented or `kernel_checked` feature, run the smallest focused check that elaborates the exact declaration.
7. If a required operation is absent, use [`$extend-hypostructure-framework`](../extend-hypostructure-framework/SKILL.md). Do not emulate it in an application.

Legacy Lean and legacy generated artifacts may be inspected only after the new mathematical contract is understood, and only as behavioral parity evidence. They may never enter a Hypostructure production import.

## Preserve the Core invariants

Design every non-root step with this shape:

```text
literal predecessor stage
  -> typed Core.Residual.Query values
  -> one local semantic certificate or primitive capability
  -> public Core/CT/domain executor
  -> framework-generated decision, trace, route, ledger extension, and work result
  -> typed terminal or named residual with a consumer
```

Require all of the following:

- one root residual and one accumulated proof ledger;
- the exact predecessor stage, or a `Core.Residual.Join` over exact paper predecessors;
- inherited facts retrieved through `Core.Residual.Query`, never copied into an output;
- decisions, focus, joins, coordinate paths, assembly, route selection, and closure owned by Core;
- graph semantics supplied by `Hypostructure.Graph` and analytic semantics supplied by `Hypostructure.PDE`;
- separate proof-ledger and mathematical closed-class-ledger reasoning;
- explicit `Core.Provision`/`Core.Metadata` separation between author primitives, inferred dependencies, and framework outputs;
- all complementary outcomes represented and every nonterminal residual assigned a typed consumer;
- only a `Core.Closure` mechanism may close a branch: direct evidence, strict progress, resource contradiction, exact imported contract, or acyclic reduction; and
- a local finite or symbolic computation with an explicit `Core.PolynomialCheckBudget`.

Reject copied predecessors, replacement residuals, application route enums, custom handoffs, caller-selected outcomes, caller-authored closure, manually composed coordinates, application gluing, detached occurrence lists, unnamed remainders, and ambient graph/context/continuum enumeration.

## Select the CT by mathematical operation

| CT | Select for |
|---|---|
| CT1 | Target realization, validation, or exact avoidance. |
| CT2 | Strict-progress deletion, replacement, or reduction. |
| CT3 | Exact response comparison under compatible contexts. |
| CT4 | Demand-to-resource assignment and capacity. |
| CT5 | Local witness aggregation into a global account. |
| CT6 | First failure in an ordered residual-owned schedule. |
| CT7 | Distinguishing context or certified response neutrality. |
| CT8 | Repeated exact state/type and response comparison. |
| CT9 | Finite label-fibre overload. |
| CT10 | Exhaustive finite classification and missing class. |
| CT11 | Localization of an additive negative deficit. |
| CT12 | Well-founded peeling with restoration. |
| CT13 | Primary resource, canonical fallback, and reconciliation. |
| CT14 | Aggregate mass, multiplicity, and capacity comparison. |
| CT15 | Target-relative rank drop or full-rank ledger. |
| CT16 | Whole-support closure and target-code comparison. |
| CT17 | Bounded scale, compatibility, survivor, or orbit arithmetic. |

Prefer the single CT whose `Spec` matches the proof operation. Read its current `Spec`, `Capability`, `State`, `Search`, `Execution`, `Theorems`, and `Automation` layers plus the matching `$implement-hypostructure-ctN` skill. Use a Graph/PDE constructor only after confirming it exists and exposes the required executor.

## Decide ownership

| Mathematical content | Owner |
|---|---|
| Residual identity, typed query, decision, join, coordinate composition, assembly, generic routing, closure, work, metadata | `Core` |
| One CT's predicates, minimal capability, search, result, trace, semantics, totality | that `CTN` |
| Reusable CT-to-CT discovery and full-ledger transition | `Routes` |
| Parameterized finite-graph objects, targets, boundaries, gluing, progress, graph CT adapters | `Graph` |
| Models, atlases, equations, observables, gauges, local/tail semantics, analytic CT adapters | `PDE` |
| Fixed theorem constants and the one local semantic instantiation | application |

Apply the vocabulary test and the Graph/PDE both-sides test. A generic-looking type parameter does not make theorem-specific mathematics generic. Conversely, repeated state, route, coordinate, or assembly plumbing is never application-owned.

## Write a decision-complete execution map

Record one row per proof step before editing Lean:

| Source obligation | Literal predecessor | Ledger queries | CT/executor | Author primitives | Framework outputs | Terminal/residual consumer | Local universe/work | Availability evidence |
|---|---|---|---|---|---|---|---|---|

For each row:

1. State the exact branch hypothesis and the single new mathematical fact.
2. Name every inherited fact and its ledger producer.
3. List only primitive caller inputs; derive searches, outcomes, routes, traces, and ledger updates in the framework.
4. Describe every complementary residual and its existing or proposed consumer.
5. Verify each cross-CT edge in `Routes.Registry`/`Routes.Accumulated` and the API matrix. A paper CT chain is not evidence that an executable route exists.
6. Identify an explicit residual-owned finite family or a symbolic coverage theorem; reject ambient exponential or continuum searches.
7. Identify a positive fixture and every complementary branch fixture. Require a non-target Graph or PDE/neutral fixture for a new generic operation.
8. Record direct source, focused build, trust, and matrix evidence. Keep parity, mathematical closure, work, integration, and publication judgments separate.

## Hand off implementation

Use [`../implement-hypostructure-proof/SKILL.md`](../implement-hypostructure-proof/SKILL.md) only after every row is expressible by current public APIs or has a framework-extension work item with an owner, residuals, fixtures, and decision record. For an Erdős node, also apply the mandatory node contract in the dedicated Erdős skill.

Finish the design only when it identifies the exact theorem, literal data flow, all typed outcomes, owners, public executors, trust inputs, practical work bounds, fixtures, and current availability evidence without leaving an implementation decision to the next agent.
