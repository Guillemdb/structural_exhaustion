---
name: design-hypostructure-proof
description: "Design a theorem as a strategy-first Hypostructure DAG. Use when translating a manuscript into registered strategy vertices, exact target/residual terminals, one accumulated ledger, domain capability inputs, and a canonical `problemDefinition : Core.Strategy.Dag.ProblemDeclaration`."
---

# Design a Hypostructure Proof

Design at the strategy level. Read the manuscript, live Core strategy API, domain adapters, and existing problem declaration before selecting implementation units.

Partition the proof into mathematically cohesive strategies with explicit inputs and exhaustive outputs. Each input is the literal previous residual plus accumulated ledger. Each output is either the registered target or a typed continuation residual.

Declare dependent edges and exhaustive branch edges in the DAG. Core derives `Program.then`, routed execution, and finalization internally. Identify only primitive domain semantics as problem inputs; schedules, routing, first-hit selection, bookkeeping, compilation, outcomes, and joins belong to the framework.

Produce a decision-complete map ending in one `Dag.Blueprint` and `ProblemDeclaration.ofDag problem strategyDag`. If a required registered strategy is unavailable, route that gap to `extend-hypostructure-framework` before application implementation.
