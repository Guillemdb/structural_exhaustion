---
name: implement-structural-exhaustion-ct10
description: Implement CT10 finite refinement classification in a structural-exhaustion Lean proof. Use for direct local data, finite class tables, a first missing class, promotion residuals, exhaustive certificates, or CT2 criticality consumers.
---

# Implement Structural Exhaustion CT10

Use CT10 to classify an explicit local datum collection, close on a direct case, or promote from the first finite class not represented.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT10") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT10/Automation.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, `Examples/CT10AutomationFirst.lean`, and `Examples/CT2ToCT10AutomationFirst.lean` completely.

## Implement the author contract

Supply datum, class, and promotion types; an explicit class `FinEnum`; class observation; direct-case predicate and decider; and promotion operator. Supply the finite local data collection in the input. The framework owns class rows, direct search, first-missing-class search, promotion state, residuals, exhaustive certificate, typed paths, soundness, and totality.

## Workflow

1. Let data be exactly the local objects exposed by the source theorem or CT2 residual.
2. Let classes be the finite refinement categories in the manuscript.
3. Define `Direct` as the independently checkable immediate-closing case.
4. Define promotion from the missing class without preselecting which class is missing.
5. Run CT10 and prove the direct, promoted, or exhaustive terminal and exact trace.
6. For CT2 criticality, obtain data through the registered `DataDiscovery` route.

## Practicality and completion

Prove a polynomial work bound from local data count times class count. Do not enumerate all refinements of an ambient graph or hide a completed promoted result in the capability. Test enabled and disabled route discovery when CT2 is the source and pin first-hit class order.
