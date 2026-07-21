---
name: implement-hypostructure-ct14
description: Implement Hypostructure CT14 aggregate mass, capacity, and multiplicity. Use for residual-owned member scans, lower-mass ledgers, optional capacities or labels, missing-data residuals, graph support or overlap bounds, PDE profile mass and capacity aggregation, and aggregate overload comparisons.
---

# Implement Hypostructure CT14

Use CT14 to compute lower mass on an exact member schedule, audit every optional capacity and label, construct canonical capacity and multiplicity ledgers, and compare aggregate lower mass with available capacity.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT14/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`;
- the applicable `Graph/CT14.lean` or `PDE/CT14.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT14.lean`;
- CT14 rows in `migration/hypostructure/api-feature-matrix.csv`, relevant PDE rows, and barrel imports.

Use only reviewed, freshly checked layers; a `planned` row is not callable. If the needed CT, domain constructor, ledger behavior, or fixture is absent or below the required status, stop and use `$extend-hypostructure-framework`. Never build an application-local parallel member ledger or aggregate decision.

## Supply only member semantics

Define `CT14.Spec` with predecessor-dependent `Member` and `Label`, plus:

- `memberLowerMass : ... -> Nat`;
- `memberCapacity : ... -> Option Nat`;
- `memberLabel : ... -> Option Label`.

Use `none` for genuinely unavailable data. Do not invent zero capacity, a default label, or a sentinel member to force a later branch.

Define `CT14.Capability` with only the exact ordered `members : Core.Residual.Query ...` read, label decidable equality, and the polynomial work envelope. The framework owns lower-mass entries and total, missing-capacity and missing-label scans, capacity entries and total, the label multiplicity function, aggregate ledger, comparison, outcome, trace, and ledger extension.

Do not enumerate the label type or label assignments. `MultiplicityLedger` folds the member schedule into a function on labels.

## Execute the aggregate audit

1. Make the member schedule the exact local family in the source inequality.
2. Prove lower mass, optional capacity, and optional label functions reflect their mathematical definitions.
3. Run `CT14.execute` or `ct14_execute` on the complete predecessor.
4. Let CT14 compute lower mass before scanning for the first unavailable capacity and then the first unavailable label.
5. Only after both scans succeed, let CT14 build `AggregateLedger` and compare upper capacity with lower mass.
6. Consume the generated ledgers and comparison evidence directly downstream.

## Discharge every outcome

Handle exactly:

- `.unboundedMember`: retained lower-mass ledger and first member with `capacity = none`;
- `.missingLabel`: lower ledger, complete capacities, and first member with `label = none`;
- `.aggregate`: exact lower, capacity, and multiplicity ledgers with `upperCapacity < lowerMass`;
- `.capacity`: the same exact ledgers with `lowerMass <= upperCapacity`.

Prove predecessor retention, `OutcomeClaim`, exact trace, totality, deterministic execution, terminal exhaustiveness, ledger-order theorems, and `checks_le_polynomial`. The complete work bound is `3 * members.card + 1`. Route every optional-data residual to a typed consumer; do not silently drop members.

## Use domain adapters

- Graph: use `Graph.CT14.aggregateSpec` and `aggregateCapability` for graph-indexed mass, support, overlap, label, or capacity semantics over predecessor-owned members.
- PDE: use `PDE.CT14.aggregateSpec` and `aggregateCapability` for represented profile mass, dyadic sums, hidden mass, or capacity aggregation over an explicit finite profile family.

Neither adapter derives the mathematical inequality relating mass to the target. Supply that theorem separately. If the proof needs real-valued or infinite aggregation not represented by the live natural-number finite contract, extend the framework instead of approximating it locally.

## Validate completion

Keep `Fixtures/CT14.lean` covering both missing-data terminals and both aggregate comparisons, exact entry order, multiplicity counts, work, Graph, and PDE adapters. Run focused checks, package build, import firewall, and trust audit. Keep parity status distinct from mathematical closure.
