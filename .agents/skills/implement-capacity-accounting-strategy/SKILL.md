---
name: implement-capacity-accounting-strategy
description: Implement a reusable Hypostructure capacity-accounting strategy. Use for deterministic charging, local witness aggregation, finite fibre overload, payer selection and fallback, mass/capacity comparison, multiplicity, graph incidence accounts, or PDE energy and flux budgets.
---

# Implement a Capacity Accounting Strategy

Read demands, payers, classes, contributions, capacities, and their finite schedules from the predecessor. Treat the budget quantity abstractly; Graph may instantiate combinatorial charge and PDE may instantiate represented energy.

Compose first eligible assignment, missing-payer localization, fibre classification, overload detection, fallback selection, and aggregate reconciliation through Core. The application supplies only primitive eligibility, contribution, and capacity laws.

Expose one registered DAG vertex with every mathematical alternative: unpaid demand, overloaded fibre, affordable ledger, aggregate excess, fallback obstruction, or exact residual. Preserve the generated assignment and accounting ledgers without copying them.

Require exact totals, exhaustive partitions, and a composed work bound. Route missing generic accounting operations through `extend-hypostructure-framework`.

Read only the previous residual and accumulated ledger.
