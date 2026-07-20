---
name: implement-structural-exhaustion-ct8
description: Implement CT8 finite repetition and response analysis in a structural-exhaustion Lean proof. Use for repeated exact types in a local state sequence, response separation, no-repetition certificates, or certified smaller-object removal.
---

# Implement Structural Exhaustion CT8

Use CT8 when the manuscript finds two states of the same exact finite type and compares their local responses to justify separation or removal.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT8") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT8/Automation.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT8AutomationFirst.lean` completely.

## Implement the author contract

Supply state, exact-type, and response-context types; explicit exact-type and response-context enumerators; the exact-type and response operators; and the input's proof-specific removal operation returning a `Core.SmallerObject`. The framework owns ordered repeated-type search, exact response comparison, no-repetition certification, response separation, removal residuals, typed paths, soundness, and totality.

## Workflow

1. Make the input sequence the bounded ordered states already constructed by the proof.
2. Define exact types and responses from finite local data.
3. Define removal only for the repeated pair selected by the framework and prove its rank decrease.
4. Run CT8 and prove the exact no-repetition, response-separation, or removal terminal and trace.
5. Consume the typed smaller object or separating coordinate without repeating the scan.

## Practicality and completion

Bound pair discovery and response comparison in terms of the sequence, type, and context counts; require a polynomial estimate. Do not generate the sequence by unbounded recursion and do not enumerate all objects of a given type. Pin first-hit order in a small fixture.

## Absolute residual-carrier rule

Never define a node-local family, subtype, image, enumeration, chosen
representative collection, or replacement carrier. The CT may inspect only
collections already owned by the literal incoming residual and retrieved
from its single accumulated ledger. If access is missing, add a generic Core
projection/query of that same residual; do not manufacture application data.
