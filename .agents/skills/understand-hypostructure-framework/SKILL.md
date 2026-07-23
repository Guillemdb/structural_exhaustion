---
name: understand-hypostructure-framework
description: Inspect and explain the live strategy-first Hypostructure framework. Use for discovering Core strategy constructors, dependent composition, routed branches, residual and ledger queries, Graph/PDE adapters, `ProblemDeclaration`, runner diagnostics, work evidence, availability, and trust boundaries.
---

# Understand the Hypostructure Framework

Treat Lean source and fresh builds as declaration truth. Distinguish implemented strategy execution from proposals and manuscript plans.

Map the public flow:

```text
Core.ProblemDefinition
  + Dag.Blueprint of registered strategies
  -> ProblemDeclaration.ofDag
  -> Core result and report
  -> unconditional theorem or exact residual
```

For a requested operation, identify the closest registered strategy, its literal predecessor type, exhaustive terminal family, domain adapter, work evidence, and target/residual consumer. Applications define only the problem and DAG; do not direct them to `Program`, `Proof`, `Chain`, contracts, ledgers, finalizers, or backend modules.

If the public strategy is missing or incomplete, recommend `extend-hypostructure-framework` and state the exact absent declaration.
