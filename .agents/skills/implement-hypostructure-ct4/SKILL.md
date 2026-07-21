---
name: implement-hypostructure-ct4
description: Implement Hypostructure CT4 deterministic charging and capacity comparison. Use for residual-owned demand and payer schedules, first-eligible assignments, missing payers, overloaded fibres, C4 certificates, capacity residuals, functional-cardinality arguments, graph vertex charging, or PDE window charging.
---

# Implement Hypostructure CT4

Use CT4 to assign each scheduled demand to its first eligible scheduled payer, then expose the first missing payer, first overloaded fibre, strict C4 gap, or complementary capacity residual.

## Gate the live contract

1. Read row `ct.ct4` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT4/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean` and `Cardinality.lean` when using the functional profile.
3. Inspect `hypostructure/Hypostructure/{Graph,PDE}/CT4.lean` and `hypostructure/Hypostructure/Fixtures/CT4.lean`.
4. Confirm live declarations and fresh `.olean` evidence, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT4.lean`. Do not equate a matrix row or source filename with a usable compiled surface.

The generic, Graph, PDE, and functional-cardinality surfaces are currently present. If any required layer or complementary outcome is absent or stale, do not replace it with application machinery; use `$extend-hypostructure-framework`.

## Supply primitive charging semantics

Define `CT4.Spec` with predecessor-indexed `Demand` and `Payer`, `Eligible`, `demandWeight`, `capacity`, and `required`.

Define `CT4.Capability` with exact `Core.Residual.Query` values for the demand and payer enumerations, a primitive eligibility decider, and a polynomial envelope for `localCheckBound`. Fix schedule order deliberately: it determines the canonical first eligible payer and all later first hits.

Prefer `CT4.FunctionalCardinalityProfile` when one payer cannot serve distinct demands and a strict schedule-cardinality gap forces a missing payer. Let that profile derive the zero-weight/zero-capacity executable instance and use `run_terminal_eq_missing` and `missingCertificate`.

Treat semantic functions, deciders, schedule queries, functional law, and work proof as author primitives or inferred predecessor reads. Treat assignment tables, fibres, totals, route decisions, terminal-indexed outcomes, trace, check count, and accumulated stage as framework outputs in `Core.Provision` metadata.

## Consume the generated outcome

1. Run `CT4.execute spec capability previous`.
2. Match only the generated terminal and typed outcome:
   - `.missingPayer` with `MissingPayerResidual`;
   - `.overloadedFibre` with `OverloadedFibreResidual`;
   - `.c4` with `C4Certificate`; or
   - `.capacity` with `CapacityResidual`.
3. Reuse the generated canonical assignment and fibre. Never rescan eligibility or rebuild a charge table in the application.
4. Prove predecessor retention, `result.verified`, `result.trace_exact`, `run_total`, determinism, outcome exhaustiveness, `checks_le_limit`, and `checks_le_polynomial`.

For graphs, use `Graph.CT4.vertexPayers`, `vertexChargingSpec`, and `vertexChargingCapability`; derive the payer schedule from the queried `FiniteObject`. For PDEs, use `PDE.CT4.windowChargingSpec` and `windowChargingCapability` with represented-state, demand, and exact window queries.

Use `Fixtures/CT4.lean` as the acceptance pattern: exercise all four neutral terminals, the functional-cardinality missing-payer result, Graph vertex overload, and PDE window capacity, with exact branch work and semantic soundness.

## Practicality and carrier rules

The visible bound is `2 * demands * payers + demands + payers + 1`. Scan only local schedules present in the incoming ledger. Never enumerate all assignments, maps, colorings, window families, or ambient objects. If a demand or payer carrier is not queryable from the literal predecessor, add the missing generic query/profile rather than authoring a node-local replacement.
