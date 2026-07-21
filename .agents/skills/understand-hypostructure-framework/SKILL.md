---
name: understand-hypostructure-framework
description: Inspect and explain the live Hypostructure framework, including Core, CT1-CT17, Routes, Graph, PDE, fixtures, migration status, ownership, execution, and trust boundaries. Use for capability discovery, architecture questions, API selection, availability checks, or orienting work before designing, implementing, reviewing, or extending a proof.
---

# Understand the Hypostructure Framework

Map what the repository proves now. Separate specification, source presence,
compiled evidence, and migration intent; do not describe the target architecture
as already executable.

## Establish authority

Work from the repository root and inspect the dirty worktree. Read, in order:

1. `HYPOSTRUCTURE_MIGRATION_GUIDE.md` for process and status semantics;
2. `DOMAIN_INDEPENDENT_CORE.md`, `GRAPH_LAYER_API.md`, and `PDE_LAYER_API.md`
   for public ownership contracts;
3. `migration/hypostructure/README.md` and the relevant CSV rows;
4. the exact modules under `hypostructure/Hypostructure`;
5. the corresponding `Hypostructure.Fixtures` and external example package.

Treat generated views and legacy StructuralExhaustion declarations as parity
evidence only. They never authorize a Hypostructure production import or API.

## Determine live availability

For every requested capability, record four independent facts:

- **specified:** the API documents assign an owner and contract;
- **implemented:** the expected Lean declarations exist in production source;
- **kernel checked:** a fresh `.olean` or focused build covers those declarations;
- **exercised:** a neutral, Graph, PDE, or application fixture executes all outcomes.

Read `migration/hypostructure/api-feature-matrix.csv`, but verify its row against
source and fresh build evidence. A `planned` registry entry is identity metadata,
not a `Core.Routing.Transition`. Source without its public executor and theorems
is an incomplete vertical slice. Never recommend an absent declaration.

## Map ownership

Use the parameterization test:

| Concern | Owner |
|---|---|
| Problems, residual ledgers, queries, decisions, focus, finite search, budgets, metadata | `Hypostructure.Core` |
| One tactic's spec, capability, state, search, execution, theorems, automation | `Hypostructure.CTN` |
| Typed CT-to-CT transition and accumulated-ledger execution | `Hypostructure.Routes` |
| Parameterized finite graph semantics and CT constructors | `Hypostructure.Graph` |
| Represented PDE semantics, local/tail structure, and PDE CT constructors | `Hypostructure.PDE` |
| Fixed constants, objects, arithmetic, and theorem-specific bridges | The application package |

Inspect `Core.Provision` and `Core.Metadata` to distinguish author primitives,
inferred dependencies, and framework outputs. Inspect `Core.Residual` for the
literal predecessor and stable residual carrier. Inspect `Routes.Registry` and
`Routes.Accumulated` separately.

## Route the next action

- Use `$design-hypostructure-proof` to select a CT chain from mathematics.
- Use `$implement-hypostructure-proof` for a domain-neutral application.
- Use `$implement-hypostructure-graph-proof` or
  `$implement-hypostructure-pde-proof` for domain registration.
- Use the matching `$implement-hypostructure-ctN` for one CT contract.
- Use `$extend-hypostructure-framework` when a required public capability is
  specified but not completely executable.
- Use `$maintain-hypostructure-migration` for parity or status records.

## Report precisely

Return the requested capability map with owner, public declarations, status,
fixtures, first consumers, missing layers, trust boundary, and recommended
skill. State which conclusions are direct source facts and which are inferences.
Do not mutate files when the request is only to understand or explain.
