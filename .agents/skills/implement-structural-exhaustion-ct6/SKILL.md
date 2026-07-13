---
name: implement-structural-exhaustion-ct6
description: Implement CT6 ordered activity failure in a structural-exhaustion Lean proof. Use for first local failures, exhaustive active ledgers, ordered closure checks, contribution totals, or a CT6-to-CT9 overload route.
---

# Implement Structural Exhaustion CT6

Use CT6 for one ordered pass that either returns the first failed local condition or certifies activity everywhere and constructs its ledger.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT6") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT6/Automation.lean`, `Spec.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, `Examples/CT6AutomationFirst.lean`, and `Examples/CT6ToCT9AutomationFirst.lean`. For the graph profile, inspect `Graph/EndpointParityCycle.lean` and `examples/even_cycle`.

## Implement the author contract

Supply the index and failure-data types, failure predicate, failure-data extractor, contribution, explicit failure order, and failure decider. The framework owns first-hit search, clean-prefix evidence, active-total computation, failure and active-ledger residuals, `ActiveLedgerRun`, typed paths, soundness, and totality.

## Workflow

1. Make indices the finite local locations checked in the proof and fix their observable order explicitly.
2. Define failure so its negation is exactly the activity statement needed later.
3. Return only local diagnostic data from `failureData`.
4. Use `runActiveLedgerOfNoFailure` or `ActiveLedgerRun` when the manuscript proves no failures independently.
5. Prove the expected first-failure or active-ledger terminal, first-hit fact, trace, and ledger semantics.
6. For a CT9 consumer, instantiate the registered route with a thin `ItemCollectionAdapter`.

## Practicality and completion

The machine performs one finite pass over the declared order. Prove its length is polynomial in the input and never use a recursively expanding frontier as the order. If frontier saturation is the actual mathematics, use `Core.FiniteSaturation.Machine` with its strict measure instead. Pin both terminal traces when both are meaningful.
