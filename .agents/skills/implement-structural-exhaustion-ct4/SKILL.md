---
name: implement-structural-exhaustion-ct4
description: Implement CT4 deterministic charging and capacity in a structural-exhaustion Lean proof. Use for finite demands, eligible payers, missing payers, overloaded fibres, functional cardinality, or aggregate capacity comparisons.
---

# Implement Structural Exhaustion CT4

Use CT4 when the proof assigns each demand to the first eligible payer and derives a missing payer, overloaded fibre, successful charge, or capacity residual.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT4") | {capability, capabilityProfiles, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT4/Automation.lean`, `Cardinality.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT4AutomationFirst.lean`. For graph coloring, inspect `Graph/GreedyColoring.lean` and `examples/greedy_coloring`.

## Implement the author contract

Supply the demand and payer types, eligibility predicate, demand weights, payer capacities, explicit demand and payer `FinEnum` values, eligibility decider, and required bound. Prefer `CT4.FunctionalCardinalityProfile` when eligibility is functional and a strict cardinality gap forces a missing payer.

The framework owns canonical first-eligible assignment, availability search, fibre construction, overload detection, capacity comparison, residuals, typed execution, soundness, and totality.

## Workflow

1. Interpret demands and payers as local finite objects already present in the proof.
2. Prove eligibility means the exact mathematical relation used by the charging step.
3. Fix enumerator order because it determines the canonical assignment.
4. Use the functional-cardinality profile when it removes irrelevant weights and capacities.
5. Run CT4 and prove the intended missing, overload, C4, or capacity terminal, residual, and trace.
6. Consume the typed residual directly; for example, use a missing payer as the constructive choice in a coloring fold.

## Practicality and completion

Bound the assignment scan by the product of local demand and payer counts and prove it polynomial in the surrounding input. Do not use all color functions or all graph maps as either universe. Test each terminal shape needed by the instance and compile the general theorem separately from its small fixture.

## Absolute residual-carrier rule

Never define a node-local family, subtype, image, enumeration, chosen
representative collection, or replacement carrier. The CT may inspect only
collections already owned by the literal incoming residual and retrieved
from its single accumulated ledger. If access is missing, add a generic Core
projection/query of that same residual; do not manufacture application data.
