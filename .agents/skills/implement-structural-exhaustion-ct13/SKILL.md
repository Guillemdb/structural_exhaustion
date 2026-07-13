---
name: implement-structural-exhaustion-ct13
description: Implement CT13 tier availability and canonical fallback in a structural-exhaustion Lean proof. Use for tier-one payer search, obstruction costs, tier-two resources, fallback reconciliation, overlap, deficit, or reconciled certificates.
---

# Implement Structural Exhaustion CT13

Use CT13 when the proof first seeks an eligible tier-one payer, then computes a canonical minimum-cost fallback and reconciles it with tier-two resources.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT13") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT13/Automation.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT13AutomationFirst.lean` completely.

## Implement the author contract

Supply the finite payer enumerator, eligibility and decider, finite obstructions, fallback default and obstruction cost, resource type and equality, obstruction-to-resource map, ordered tier-two resources, charge, and demand. The framework owns tier-one search, explicit absence, canonical minimum-cost fallback, reconciliation, comparison, residuals, certificate, typed execution, soundness, and totality.

## Workflow

1. Make payers, obstructions, and resources local to the selected branch.
2. Fix payer and obstruction orders because first-hit and minimum-cost tie-breaking are observable.
3. Prove costs and charges are exactly the quantities used by the manuscript.
4. Run CT13 and prove the tier-one, overlap, deficit, or reconciled terminal and exact trace.
5. Consume the selected fallback and ledger from the typed outcome rather than recomputing them.

## Practicality and completion

Bound both finite searches and reconciliation by polynomial functions of the local payer, obstruction, and tier-two sizes. Do not enumerate global resource assignments. Test all terminal modes reachable by the application and pin canonical tie-breaking.
