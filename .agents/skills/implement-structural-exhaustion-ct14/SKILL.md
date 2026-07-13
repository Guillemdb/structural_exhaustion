---
name: implement-structural-exhaustion-ct14
description: Implement CT14 aggregate mass and multiplicity in a structural-exhaustion Lean proof. Use for finite member scans, lower masses, optional capacities, labels, multiplicity ledgers, missing labels, or aggregate capacity comparisons.
---

# Implement Structural Exhaustion CT14

Use CT14 to retain a computed lower mass while scanning every local member for capacity and label data, then compare the aggregate ledgers.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT14") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT14/Automation.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT14AutomationFirst.lean` completely.

## Implement the author contract

Supply the member type and explicit enumerator, label type and decidable equality, per-member lower mass, optional capacity, and optional label. The framework owns lower-mass summation, complete member scan, multiplicity and upper-capacity ledgers, comparison, residuals, aggregate certificate, typed execution, soundness, and totality.

## Workflow

1. Make members the finite local family appearing in the source inequality.
2. Represent genuinely unavailable bounds or labels with `Option`; do not fabricate defaults.
3. Prove lower masses, capacities, and labels reflect the mathematical definitions.
4. Run CT14 and prove the unbounded-member, missing-label, aggregate, or capacity terminal and trace.
5. Reuse the generated multiplicity and capacity ledger in downstream arithmetic.

## Practicality and completion

The machine scans the member enumerator a constant number of times. Prove its size and arithmetic cost are polynomial in the input. Do not enumerate label assignments or member subsets. Test every optional-data failure used by the theorem and at least one successful aggregate comparison.
