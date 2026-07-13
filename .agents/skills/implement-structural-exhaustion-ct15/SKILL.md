---
name: implement-structural-exhaustion-ct15
description: Implement CT15 target-relative rank and full-rank ledgers in a structural-exhaustion Lean proof. Use for finite rank coordinates, target dependence, first rank drops, charge ledgers, C4 certificates, or capacity residuals.
---

# Implement Structural Exhaustion CT15

Use CT15 to compute target-relative rank over explicit local coordinates, return the first drop, or compare the full-rank charge ledger with capacity.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT15") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT15/Automation.lean`, `Spec.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT15AutomationFirst.lean` completely.

## Implement the author contract

Supply coordinate type, target-dependence predicate, charge and capacity functions, explicit coordinate `FinEnum`, and target-dependence decider. The framework owns rank contributions, computed rank, first-drop search, full-rank ledger entries and total, capacity comparison, residuals, C4 certificate, typed execution, soundness, and totality.

## Workflow

1. Make coordinates the finite local rank components from the manuscript.
2. Prove the target-dependence decider reflects the exact semantic predicate.
3. Define charge and capacity in the same units as the final inequality.
4. Run CT15 and prove the rank-drop, C4, or full-rank-ledger terminal and exact trace.
5. Extract the first coordinate or generated ledger from the typed outcome.

## Practicality and completion

Bound all work by a constant number of passes over local coordinates and polynomial-time charge evaluation. Do not make coordinates range over all target substructures. Test the first-hit rank drop and both full-rank comparison outcomes needed by the instance.
