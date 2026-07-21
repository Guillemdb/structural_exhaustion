---
name: implement-hypostructure-ct7
description: Implement Hypostructure CT7 exact context classification. Use for a target realization in one finite context, a first distinguishing context after target failure, certified universal response neutrality, same-boundary graph contexts, or additive PDE local-tail contexts.
---

# Implement Hypostructure CT7

Use CT7 to search the left representative for a target realization and, only after exhaustive failure, compare two representatives on the same exact context-coordinate schedule.

## Gate the live contract

1. Read row `ct.ct7` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT7/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean` and the referenced `Core/Response` finite-table modules.
3. Inspect `hypostructure/Hypostructure/{Graph,PDE}/CT7.lean` and `hypostructure/Hypostructure/Fixtures/CT7.lean`.
4. Confirm the live declarations and fresh `.olean` evidence, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT7.lean`. Never claim availability from the migration row without matching source and kernel evidence.

The generic, Graph, and PDE exact-context surfaces are currently present. If a needed context model, coverage theorem, outcome, or route is missing, do not insert an application-level classifier; use `$extend-hypostructure-framework`.

## Supply exact response semantics

Define `CT7.Spec` with a representative type, `Core.Response.System`, and `Realizes` on semantic contexts.

Define `CT7.Capability` with:

- a `Core.Residual.Query` for the exact source/replacement pair;
- a `Core.Residual.Query` for the exact coordinate schedule;
- response-value equality;
- a primitive scheduled-realization decider;
- semantic realization coverage; and
- symbolic response coverage for the same schedule.

Use `Capability.ofExactContexts` only when every semantic context literally occurs in the queried coordinate schedule. Otherwise provide the two weaker coverage laws directly; never assert completeness for convenience. The framework derives the linear work budget `2 * contexts.card`.

Treat response and realization semantics, typed queries, primitive decisions, and coverage as author primitives. Treat scan order, first hits, exhaustive states, terminal, outcome, trace, work, and accumulated ledger extension as framework outputs in `Core.Provision` metadata.

## Execute the ordered classification

1. Run `CT7.execute spec capability previous`.
2. Consume one generated outcome:
   - `.realization` with `RealizationCertificate`;
   - `.distinguishing` with `DistinguishingResidual`, including universal non-realization and a concrete response mismatch; or
   - `.neutral` with `NeutralityCertificate`, including universal non-realization and universal exact response equality.
3. Use `NeutralityCertificate.target_iff` only with an exact registered `TargetSemantics`.
4. Prove predecessor retention, `result.verified`, `result.trace_exact`, the appropriate terminal-forcing theorem, `run_total`, determinism, outcome exhaustiveness, and the linear polynomial bound.

For graphs, use `Graph.CT7.targetSpec`, `targetCapabilityOfExactContexts`, `realization_target`, and `neutrality_target_iff` over same-boundary gluing. For PDEs, use `PDE.CT7.targetSystem`, `targetSemantics`, `targetSpec`, and `targetCapabilityOfExactContexts` for additive local-tail assembly.

Use `Fixtures/CT7.lean` as the minimum: exercise all three neutral terminals and exact work/traces, a Graph realization, and a PDE distinction with semantic soundness.

## Practicality and carrier rules

Enumerate only exact local context coordinates supplied by the predecessor. Use symbolic coverage for an infinite ambient context type. Never enumerate all outside graphs, tails, gauges, topologies, or target shells, and never replace the residual schedule with a node-local classifier output.
