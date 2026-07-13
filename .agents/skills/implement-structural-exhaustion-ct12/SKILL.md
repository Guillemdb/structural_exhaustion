---
name: implement-structural-exhaustion-ct12
description: Implement CT12 well-founded structural peeling in a structural-exhaustion Lean proof. Use for finite peeling schedules, saturation, restoration choices, demand or tier residuals, bounded iterations, or list-peeling profiles.
---

# Implement Structural Exhaustion CT12

Use CT12 for a recursive peeling argument only when every continuation carries an explicit strict decrease consumed by the framework's well-founded runner.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT12") | {capability, capabilityProfiles, loopDecrease, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT12/Automation.lean`, `ListPeeling.lean`, `DisjointPacking.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, `Core/FiniteDisjointPacking.lean`, `Examples/CT12AutomationFirst.lean`, `Graph/GreedyColoring.lean`, `Graph/InducedPathPacking.lean`, `examples/greedy_coloring`, and `examples/even_cycle/EvenCycleExample/CT12MaximalMatching.lean`.

## Implement the author contract

Supply indexed state, peeled object, demand-residual, and tier-residual types; the peel operator; and nonempty restoration options whose continuation branch proves strict decrease. Prefer `CT12.ListPeeling` for a concrete finite schedule.

For maximum/maximal families of nonempty finite supports, use
`CT12.DisjointPacking.Profile`. Supply only the finite item type, host vertex
schedule, support map, and one representative vertex per support. The core
selects a maximum disjoint family and proves saturation; CT12 audits only its
selected list, proves that the iteration count equals the selected-list
length, and derives a host-vertex iteration bound. Do not construct or execute
an enumeration of all items or all packings.

The framework owns saturation decisions, peel states, first restoration selection, decrease verification, the well-founded loop, bounded-iteration and bounded-trace theorems, residuals, typed execution, soundness, and totality.

## Workflow

1. Define the state index and measure before the step function.
2. Make `peel` perform one local structural removal or report saturation.
3. Make each restoration option either close with a typed residual or return a state with a proved smaller measure.
4. Use `ListPeeling` when the measure is remaining list length.
5. Run the framework loop; never write a parallel recursive executor in the application.
6. Prove the exhausted, demand, or tier terminal, exact trace, iteration bound, and semantic theorem.
7. For a packing stage, prove both maximum cardinality and maximal saturation,
   retain the exact iteration count and support/remainder cardinality
   identities, and derive remainder avoidance from saturation.

## Practicality and completion

Require a polynomial bound on both iteration count and work per iteration. Reject recursion whose next frontier grows without a decreasing global measure, even if each individual state is finite. Test zero, one-step residual, and multi-step exhaustion cases relevant to the capability.
