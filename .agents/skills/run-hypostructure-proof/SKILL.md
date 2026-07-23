---
name: run-hypostructure-proof
description: "Run and certify an end-to-end Hypostructure proof from a problem file exporting `problemDefinition : Core.Strategy.Dag.ProblemDeclaration`. Use to determine whether a strategy DAG proves the registered target unconditionally or returns an exact typed residual, and to kernel-check the resulting theorem or reduction."
---

# Run a Hypostructure Proof

Accept one application entry point: `problemDefinition`, created by `ProblemDeclaration.ofDag` from one registered problem and one DAG blueprint. Do not manually instantiate `Hypostructure`, compiled chains, or outputs.

## Execute

Build only the application declaration and its import closure. Kernel-check `problemDefinition.result` and inspect `problemDefinition.report`, whose certified outcome is either the official statement or the exact total residual.

## Certify the result

Compilation alone is not evidence of unconditional closure. Require one of:

- a theorem obtained automatically when the compiled residual family is empty;
- the automatic `problemDefinition.result` theorem exposing target or the exact dependent residual.

Never guess which side of the output holds, manufacture a residual, invoke a finalizer, or replace the Core report with a claimed runtime evaluation.

## Report

State exactly what the kernel checks: unconditional theorem, unconditional reduction with residual type, or build failure. Include relevant axiom output and distinguish framework axioms from application assumptions.
