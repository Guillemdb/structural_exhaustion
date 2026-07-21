---
name: implement-hypostructure-ct11
description: Implement Hypostructure CT11 finite additive-deficit localization. Use for exact negative totals, first inadmissible cells, first locally negative cells, graph degree or support budgets, PDE window or error-channel budgets, and the ordered negative-budget profile.
---

# Implement Hypostructure CT11

Use CT11 to turn a strict negative total over one predecessor-owned finite order into either the first admissibility gap or the first admissible cell with negative local budget.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT11/{Spec,Capability,State,Search,Execution,Theorems,Automation,NegativeBudget}.lean`;
- the applicable `Graph/CT11.lean` or `PDE/CT11.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT11.lean`;
- the CT11 rows in `migration/hypostructure/api-feature-matrix.csv`, the relevant PDE row, and public barrel imports.

Require reviewed status plus a fresh focused fixture before application use. A `planned` row is not callable. If any required vertical-slice or domain layer is absent or not sufficiently checked, stop and use `$extend-hypostructure-framework`. Do not write an application-local scan, negative-cell chooser, or copied deficit carrier. Use `$implement-hypostructure-route` only for a missing cross-CT edge after both CTs are available.

## Supply only primitive mathematics

Define `CT11.Spec` with predecessor-dependent `Cell`, `Admissible`, and `localBudget : ... -> Int`.

Define `CT11.Capability` with:

- an ordered `cells` enumeration read by `Core.Residual.Query`;
- `admissibleDecidable`;
- `negativeTotal`, also a typed query, proving the sum of `localBudget` over that exact queried list is strictly negative;
- the polynomial work envelope.

Prove any global algebraic identity outside CT11, store its exact consequence in the predecessor ledger, and query it. Never detach a different decomposition or change the order between the total theorem and the scan.

Use `CT11.OrderedNegativeBudgetProfile` when every scheduled cell is definitionally admissible. Do not replace it with a bespoke application profile.

## Execute the two-pass localization

1. Choose cells as the literal finite terms, graph occurrences, windows, or channels in the source sum.
2. Prove the strict negative total for precisely `cells.values.map localBudget`.
3. Run `CT11.execute` or `ct11_execute` on the complete predecessor.
4. Let Core scan first for `¬ Admissible`; only after exhaustive admissibility let it scan for `localBudget < 0`.
5. Consume the selected residual from `result.outcome`; never preselect a cell or reconstruct its prefix facts.

The exhaustive no-negative branch is eliminated by the registered strict-negative total. Do not add a third public terminal or hide a nonnegative-total assumption.

## Discharge every outcome

Handle exactly:

- `.admissibilityGap`: the canonical first `AdmissibilityGapResidual`, with membership, inadmissibility, and admissible prefix;
- `.localizedDeficit`: `LocalizedDeficitResidual`, with all scheduled cells admissible, selected-cell membership and negativity, nonnegative prefix, and the retained negative total.

Prove predecessor equality, `OutcomeClaim`, exact terminal trace, terminal exhaustiveness, deterministic execution, exact branch work, totality, and `checks_le_polynomial`. The complete envelope is two scans, `2 * cells.card`. Give every residual an explicit typed consumer.

## Use the domain adapters

- Graph: use `Graph.CT11.additiveSpec` and `additiveCapability`, or `negativeBudgetProfile` for the everywhere-admissible case. Read the finite graph through a query; keep the cell schedule residual-owned.
- PDE: use `PDE.CT11.additiveSpec`, `additiveCapability`, or `negativeBudgetProfile`. Enumerate only supplied windows or channels of a represented state, never a continuum or an implicit decomposition family.

If the mathematical budget is not integer-valued, or localization requires measure-theoretic selection rather than an explicit finite family, record the mismatch and extend the framework. Do not coerce the theorem into an unsound finite surrogate.

## Validate completion

Keep `Fixtures/CT11.lean` covering both terminals, first-hit order, the ordered negative-budget profile, exact checks and traces, and Graph/PDE adapters. Run focused source and fixture checks, then package, import-firewall, and trust validation. Report parity and mathematical closure independently.
