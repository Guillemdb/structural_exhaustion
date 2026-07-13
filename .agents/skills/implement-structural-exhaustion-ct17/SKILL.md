---
name: implement-structural-exhaustion-ct17
description: Implement CT17 finite target thickening and survivor arithmetic in a structural-exhaustion Lean proof. Use for bounded compatibility searches, finite scale splits, survivor enumeration, target hits, incompatibility, or orbit residuals.
---

# Implement Structural Exhaustion CT17

Use CT17 only for the bounded target, offset, scale, position, and arithmetic universes explicitly present in the proof.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT17") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT17/Automation.lean`, `Spec.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT17AutomationFirst.lean` completely.

## Implement the author contract

Supply target, offset, position, and value types; target, block, and orbit value functions; compatibility predicate; explicit target, offset, and position enumerators; compatibility and value-equality deciders; and a finite scale limit. The framework owns compatibility search, scale split, survivor enumeration, arithmetic analysis, residuals, certificates, typed execution, soundness, and totality.

## Workflow

1. Derive targets, offsets, positions, and scale limit from the manuscript's finite bounded range.
2. Define values and compatibility as direct local arithmetic operations.
3. Prove deciders reflect those predicates.
4. Run CT17 and prove the incompatibility, exhausted, survivors, target-hit, or orbit terminal and exact trace.
5. Extract the survivor or orbit residual from the typed outcome without rerunning enumeration.

## Practicality and completion

Prove a polynomial bound for the product of targets, offsets, bounded scales, and positions. Reject a scale limit derived from open-ended search or recursion and never materialize an infinite orbit. Test each reachable terminal and boundary scales zero and the declared maximum.
