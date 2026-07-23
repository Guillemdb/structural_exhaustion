---
name: implement-hypostructure-proof
description: Implement an end-to-end Lean theorem as one `Core.ProblemDefinition` plus one registered `Dag.Blueprint`. Use for Graph/PDE strategy selection, canonical `ProblemDeclaration.ofDag`, Core execution, and a kernel-certified unconditional theorem or exact total residual.
---

# Implement a Hypostructure Proof

Read the live DAG API and manuscript authority. Register one `Core.ProblemDefinition` containing the ambient problem, baseline, branch-state carrier and initializer, target predicate, and official statement bridge.

Implement the proof as a declarative DAG of registered strategies. Declare only registered vertices and typed edges; Core derives sequencing, routing, joins, retained witnesses, early target closure, and the final residual union. Extend the framework when a generic registered vertex is missing.

Export exactly the problem, DAG, and canonical runner declaration:

```lean
def problem : Core.ProblemDefinition := ...

def strategyDag : Core.Strategy.Dag.Blueprint
    (Core.Strategy.ProblemInput problem.problem) := ...

noncomputable def problemDefinition : Core.Strategy.Dag.ProblemDeclaration :=
  Core.Strategy.Dag.ProblemDeclaration.ofDag problem strategyDag
```

Kernel-check `problemDefinition.result` and inspect `problemDefinition.report` for every DAG. Core proves the official statement automatically when the compiled total residual is empty. Never construct `Proof`, `Chain`, `OutputStrategy`, `Contract`, terminal sums, ledgers, finalizers, or outcomes in application code.

Validate focused imports, work bounds, predecessor preservation, axiom output, and absence of manuscript-node dependencies.
