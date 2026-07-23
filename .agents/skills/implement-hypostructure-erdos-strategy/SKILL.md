---
name: implement-hypostructure-erdos-strategy
description: Translate a cohesive block of the original Erdős--Gyárfás Problem 64 proof into its node-free registered `Dag.Blueprint`. Use when extending the EG DAG from the paper or frozen proof and reading the resulting theorem or exact residual from Core's report.
---

# Implement an Erdős--Gyárfás Strategy

Treat the original paper and frozen structural-exhaustion proof as mathematical authority. Use `EG_CHAPTER1_STRATEGY_TRANSLATION_PLAN.md` for the strategy-block map and live Lean source for available APIs.

## Preserve the application boundary

The EG application may define only one `Core.ProblemDefinition` and one `Dag.Blueprint`. Problem-owned inputs include its target semantics and irreducible certified finite tables; the DAG names only registered Core/Graph strategies and typed edges. Import no manuscript `NodeX` module. Do not recreate node payloads, routing records, budgets, outcomes, or branch labels.

## Translate one cohesive paper block

Start from the literal residual produced by the preceding strategy. Select the reusable strategy patterns matching the paper block, compose them through Core, and preserve the accumulated ledger. Type A/Type B are application names for a generic routed dichotomy, not Core concepts.

Every terminal must match a paper conclusion or an exact continuation residual. No placeholder outcome, assumed closure, or manually manufactured payload is allowed.

## Integrate and validate

Extend the single EG `Dag.Blueprint` and rebuild `problemDefinition` only through `ProblemDeclaration.ofDag`. Inspect Core's automatic report and kernel-check its theorem or exact total residual. Compare semantics with the frozen proof without importing it into production.
