---
name: implement-hypostructure-ct16
description: Implement Hypostructure CT16 whole-support closed-code exhaustion. Use for residual-owned finite support scans, first missing coordinates, one directly computed closed code, literal target-code equality or mismatch, graph vertex-support codes, and PDE compactified finite-class audits.
---

# Implement Hypostructure CT16

Use CT16 to audit one complete predecessor-owned coordinate schedule, compute exactly one closed code after whole support is established, and compare it literally with the target code.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT16/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`;
- the applicable `Graph/CT16.lean` or `PDE/CT16.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT16.lean`;
- CT16 rows in `migration/hypostructure/api-feature-matrix.csv`, relevant PDE rows, and barrel imports.

Require reviewed status and fresh focused evidence; a `planned` row is not callable. If whole-support semantics, a domain code adapter, target-completeness machinery, or an expected route is missing, pause and use `$extend-hypostructure-framework` or `$implement-hypostructure-route` as appropriate. Never author an application-local closed-class ledger or terminal to bypass the missing layer.

## Supply only support and code semantics

Define `CT16.Spec` with:

- predecessor-dependent `Coordinate`;
- primitive `InSupport`;
- predecessor-dependent `ClosedCode`;
- one directly computed `closedCode` and one `targetCode`.

Define `CT16.Capability` with the exact coordinate enumeration as `Core.Residual.Query`, a support decider, and code decidable equality. CT16 derives its own linear budget: one support check per coordinate, one code computation, and one equality decision, bounded by `coordinates.card + 2`.

Do not enumerate candidate codes or closed structures. Do not provide whole-support evidence, a computed-code state, equality verdict, mismatch residual, result, or trace.

## Execute the whole-support audit

1. Make the coordinate query the complete finite support indices justified by the predecessor.
2. Prove `InSupport` is the exact primitive local predicate and its decider reflects it.
3. Compute `closedCode` directly from the predecessor; do not search for a code.
4. State the intended target as literal equality with `targetCode`, adding a semantic equivalence theorem separately if the paper uses another presentation.
5. Run `CT16.execute` or `ct16_execute`.
6. Consume the generated terminal evidence from the accumulated stage.

## Discharge every outcome

Handle exactly:

- `.properSupport`: the first scheduled coordinate outside support, with membership, absence, and present prefix;
- `.exactCode`: whole support plus literal `closedCode = targetCode` as `ExactClosedType`;
- `.mismatch`: whole support plus the exact computed-code inequality.

Prove predecessor retention, `OutcomeClaim`, exact trace, support-check and total-check equations, linear polynomial work, terminal exhaustiveness, deterministic execution, and totality. Route both proper-support and mismatch residuals to named typed consumers.

An exact-code terminal proves equality only for the declared schedule and code semantics. It does not by itself establish global target completeness, close every compactified class, or prove a final theorem. Require the relevant closed-ledger and target theorem before claiming those consequences.

## Use domain adapters

- Graph: use `Graph.CT16.vertexCoordinates`, `vertexSpec`, and `vertexCapability`; the packed graph supplies its exact vertex schedule.
- PDE: use `PDE.CT16.compactifiedSpec` and `compactifiedCapability` with an explicit residual-owned coordinate schedule over a represented object.

Neither adapter may manufacture windows, profiles, graph subobjects, state spaces, or a code universe. Missing representation belongs in the domain layer.

## Validate completion

Keep `Fixtures/CT16.lean` covering proper support, exact code, mismatch, first-missing order, exact checks and traces, and Graph/PDE adapters. Run focused checks followed by package, firewall, and trust validation. For PDE row 18 or another final audit, separately verify that all prior closed classes propagate and the target-completeness executor is actually present.
