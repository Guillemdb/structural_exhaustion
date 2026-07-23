---
name: implement-hypostructure-graph-proof
description: Implement finite graph theorems as Hypostructure strategy programs. Use for Graph problem/target registration, isomorphism semantics, residual-owned graph queries, reusable strategy specialization, and a node-free `problemDefinition` executed by Core.
---

# Implement a Hypostructure Graph Proof

Keep the application to two values: one `Core.ProblemDefinition` and one `Dag.Blueprint`. Register packed finite graphs, baseline, initial branch state, target, and isomorphism laws in the problem. Supply reusable Graph registered strategies for graph semantics.

Compose public Core strategies for the proof. Graph code supplies semantic facts only; it does not implement generic scans, branch routing, ledger management, first-hit selection, or output diagnostics.

Create `problemDefinition` only with `ProblemDeclaration.ofDag problem strategyDag`, then inspect Core's report. Add a reusable Graph adapter only when the same semantic operation can support more than the current application. Never build outputs, routes, ledgers, or finalizers in the graph application.
