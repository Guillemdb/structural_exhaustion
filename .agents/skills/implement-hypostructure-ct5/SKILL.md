---
name: implement-hypostructure-ct5
description: Implement Hypostructure CT5 local-witness aggregation over a resource budget. Use for active sites, dependent finite witness fibres, first support deficits, generated contribution ledgers, C4 affordability failure, bounded charge ledgers, aggregate excess, graph local accounts, or PDE energy and flux accounts.
---

# Implement Hypostructure CT5

Use CT5 to find the first active site without support or, after exhaustive support, aggregate one canonical witness contribution per scheduled site in a registered resource budget.

## Gate the live contract

1. Read row `ct.ct5` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT5/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean` and `Core/Budget/Resource.lean`.
3. Inspect `hypostructure/Hypostructure/{Graph,PDE}/CT5.lean` and `hypostructure/Hypostructure/Fixtures/CT5.lean`.
4. Confirm current source and fresh `.olean` evidence, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT5.lean`. Treat `api-feature-matrix.csv` as a reviewed ledger, not executable proof.

The generic, Graph, and PDE slices are currently present. If the resource algebra, residual branch, domain constructor, or theorem needed by the proof is missing, forbid a local substitute and use `$extend-hypostructure-framework`.

## Define the author surface

Define `CT5.Spec` with a `Core.ResourceBudget`, predecessor-indexed sites and dependent witnesses, `Active`, `Supports`, `contribution`, `required`, and `capacity`.

Define `CT5.Capability` with one `Core.Residual.Query` returning the exact `Core.Finite.DependentEnumeration` of sites and witness fibres, primitive activity and support deciders, and decidable resource order. Obtain it from the literal predecessor with typed query composition; never pass an application-built deficit or ledger.

The framework derives `sitesAt`, each `witnessesAt`, the canonical first support, the contribution ledger and total, and `linearWorkBudget`. Do not add an author-selected witness, sum, branch, or custom check count. Classify the resource semantics, local predicates, contributions, deciders, and family query as author primitives or inferred inputs; classify all scans, comparisons, outcomes, trace, ledger, and accumulated stage as framework outputs in `Core.Provision`.

## Execute the fixed-priority flow

1. Call `CT5.execute spec capability previous`.
2. Consume exactly one generated outcome:
   - `.deficit` with `LocalDeficitResidual`;
   - `.c4` with `C4Certificate` when capacity cannot meet `required`;
   - `.chargeLedger` with a bounded `ChargeLedgerResidual`; or
   - `.aggregate` with `AggregateResidual` after required affordability but total capacity failure.
3. Reuse `DeficitFreeState`, `LocalLedgerState`, and their semantic theorems; never repeat support search or summation downstream.
4. Prove literal predecessor retention, `result.verified`, `result.trace_exact`, `run_total`, determinism, outcome exhaustiveness, `checks_le_limit`, and `checks_le_polynomial`.

For graphs, use `Graph.CT5.localWitnessSpec` and `localWitnessCapability` against a queried `FiniteObject`. For PDEs, use `PDE.CT5.localWitnessSpec` and `localWitnessCapability` against a queried represented state. Both adapters evaluate domain semantics only; CT5 still owns the family scan, account, comparisons, and route.

Use `Fixtures/CT5.lean` as the minimum: exercise all four neutral terminals, exact traces and work, Graph charge-ledger behavior, and PDE aggregate behavior.

## Practicality and carrier rules

The complete bound is `flatten.card + 2 * indices.card + 2`. Keep sites and dependent witness fibres finite, explicit, local, and predecessor-owned. Never use ambient graphs, arbitrary subsets, recursively generated witnesses, continuum points, or a detached node-local family. Add a reusable Core or domain abstraction if the incoming ledger lacks the necessary dependent query.
