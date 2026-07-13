---
name: implement-structural-exhaustion-ct16
description: Implement CT16 exact whole-support closed types in a structural-exhaustion Lean proof. Use for finite support scans, proper-support residuals, closed-code computation, target-code equality, or closed-type mismatch residuals.
---

# Implement Structural Exhaustion CT16

Use CT16 to exhaust an explicit coordinate support, compute one closed code, and split by literal equality with the target code.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT16") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT16/Automation.lean`, `Types.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT16AutomationFirst.lean` completely.

## Implement the author contract

Supply coordinate and closed-code types, explicit coordinate `FinEnum`, support predicate and decider, closed-code computation, target code, and decidable code equality. The framework owns exhaustive support scanning, exact code computation, literal equality comparison, residuals, certificate, typed execution, soundness, and totality.

## Workflow

1. Choose coordinates as the complete finite support indices proved relevant by the source.
2. Make `InSupport` a primitive local check with a reflection-correct decider.
3. Compute `closedCode` directly from the branch object; do not search over possible codes.
4. Run CT16 and prove the proper-support, exact-code, or mismatch terminal and trace.
5. Consume the typed support coordinate or code equality evidence directly.

## Practicality and completion

Bound support scanning and code computation polynomially in the local coordinate count. Do not enumerate closed structures or candidate codes. Test all three terminal modes when meaningful and pin the exact computed code in the successful fixture.
