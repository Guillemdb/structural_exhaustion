---
name: implement-structural-exhaustion-ct7
description: Implement CT7 exact context classification in a structural-exhaustion Lean proof. Use for finite realization contexts, response distinctions between two objects, distinguishing-context residuals, or certified response neutrality.
---

# Implement Structural Exhaustion CT7

Use CT7 to search for a realization and, only after exhaustive absence, compare two objects across the same finite local contexts.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT7") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT7/Automation.lean`, `Spec.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT7AutomationFirst.lean` completely.

## Implement the author contract

Supply the object and context types, realization predicate, exact response function, explicit context `FinEnum`, and realization decider. The input supplies the object pair. The framework owns realization search, response distinction search, neutrality, residual construction, typed execution, soundness, and totality.

## Workflow

1. Define contexts as the finite external tests named by the proof.
2. Make realization mean precisely that the first object closes the branch in that context.
3. Make the response value an exact, computable local observation for either object.
4. Run CT7 and prove the realization, distinguishing, or neutral terminal and exact trace.
5. Use the distinguishing residual's concrete context or the neutrality certificate directly in the next theorem.

## Practicality and completion

Enumerate only the local comparison contexts, never all ambient completions. Bound realization and response checks by a constant number of passes over this enumerator and prove the resulting polynomial estimate. Test all three terminal families if the application can reach them.
