---
name: implement-hypostructure-pde-proof
description: Implement represented PDE arguments as Hypostructure strategy programs. Use for PDE problem/target registration, represented observables and budgets, reusable strategy specialization, explicit analytic provisions, and a canonical `problemDefinition` executed by Core.
---

# Implement a Hypostructure PDE Proof

Separate represented finite execution from analytic provisions. Register local models, observables, schedules, equations, representations, initial state, and target semantics in one `Core.ProblemDefinition`.

Use the same public Core strategies as Graph proofs for ordered exhaustion, response classification, accounting, localization, target avoidance, rank/budget splits, and closed-code exhaustion. PDE supplies only analytic meanings and soundness laws.

Keep energy, flux, norms, and compactness quantities abstract through registered budget interfaces. Do not reimplement Core routing or bookkeeping in PDE.

Define one `Dag.Blueprint`, create the runner only with `ProblemDeclaration.ofDag problem strategyDag`, and report Core's certified outcome together with the remaining analytic trust boundary. PDE application code never constructs execution or outcome objects.
