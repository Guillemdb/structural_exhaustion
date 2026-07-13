---
name: implement-structural-exhaustion-ct9
description: Implement CT9 exact label-fibre overload in a structural-exhaustion Lean proof. Use for finite pigeonhole arguments, overloaded label fibres, bounded partitions, capacity-one pairs, parity pairs, or CT6 active-ledger consumers.
---

# Implement Structural Exhaustion CT9

Use CT9 to partition an explicit duplicate-free local item collection by finitely many labels and locate the first overloaded fibre.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT9") | {capability, capabilityProfiles, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT9/Automation.lean`, `ParityCapacityOne.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, `Examples/CT9AutomationFirst.lean`, and `Examples/CT6ToCT9AutomationFirst.lean`. Inspect `Graph/EndpointParityCycle.lean` for the parity profile.

## Implement the author contract

Supply item and label types, explicit label `FinEnum`, label map, and capacity. Supply the actual local items as an `OrderedCollection` in the input or route trigger. The framework owns fibres, duplicate-freeness, total capacity, overload search, bounded certificates, same-label pairs, `OverloadedRun`, typed paths, soundness, and totality.

Prefer `CT9.ParityCapacityOneSpec` when labels are parity bits from a rank map and every capacity is one.

## Workflow

1. Obtain items from an already constructed local collection; preserve their observable order and prove no duplicates.
2. Define labels and capacities exactly as in the counting inequality.
3. Prove total capacity is smaller than item cardinality when forcing overload.
4. Use the framework theorem producing an `OverloadedRun` or parity-capacity-one run.
5. Extract the typed same-label pair and prove the expected terminal and trace.
6. Use the registered CT6-to-CT9 adapter when items come from an active ledger.

## Practicality and completion

Only enumerate labels and scan the supplied local items. Never enumerate all partitions or all subsets. Prove a polynomial work bound from the product of item and label counts, test both overload and bounded terminals where meaningful, and pin the selected first overloaded label.
