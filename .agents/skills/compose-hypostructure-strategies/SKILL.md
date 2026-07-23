---
name: compose-hypostructure-strategies
description: Declare a valid Hypostructure `Dag.Blueprint` from registered strategies. Use for typed edges, exhaustive dichotomies, branch-local continuations, joins, early target closure, total residual unions, and `ProblemDeclaration.ofDag`.
---

# Compose Hypostructure Strategies

Work only through the public declarations in `Hypostructure.Core.Strategy.Dag` and registered Core/domain strategy constructors.

## Establish the boundaries

Read the incoming strategy types and their literal residual queries. Confirm that each strategy consumes the complete previous stage and returns a framework-owned ledger extension. Reject detached payloads, copied fields, application-defined routing, and reconstructed predecessors.

## Compose

Declare only the strategy vertices and their typed DAG edges, including every exhaustive branch. Core derives dependent composition and routed execution, preserves every branch witness in the joined ledger, stops target branches, and joins every open leaf into the final typed residual sum.

Aggregate checks and work in execution order. For exclusive branches, use the framework's branch work rule rather than summing work that cannot occur together.

## Produce the application DAG

The final value must be one `Core.Strategy.Dag.Blueprint (Core.Strategy.ProblemInput problem.problem)`. Pass it with the registered `Core.ProblemDefinition` to `Core.Strategy.Dag.ProblemDeclaration.ofDag`. Never construct `Proof`, `Chain`, `OutputStrategy`, `Contract`, `Ledger.Extension`, `Sum.inl`, `Sum.inr`, or call `Program.finish` in an application.

If the required composition primitive does not exist, use `extend-hypostructure-framework`; do not add glue in the application.

## Validate

Build the smallest importing module. Inspect Core's `problemDefinition.result` and `problemDefinition.report`; verify predecessor/object preservation, exhaustive terminal coverage, and the exact total residual. Check that the application imports no manuscript node module.
