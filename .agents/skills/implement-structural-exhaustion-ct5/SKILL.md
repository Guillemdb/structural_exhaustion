---
name: implement-structural-exhaustion-ct5
description: Implement CT5 local witness aggregation in a structural-exhaustion Lean proof. Use for active sites, dependent witnesses, support deficits, contribution ledgers, charge bounds, or aggregate comparisons.
---

# Implement Structural Exhaustion CT5

Use CT5 to search local sites for unsupported witnesses and otherwise aggregate their certified contributions.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT5") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT5/Automation.lean`, `Spec.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT5AutomationFirst.lean` completely.

## Implement the author contract

Supply local sites, the dependent witness family, active and support predicates, contributions, explicit site and per-site witness enumerators, primitive deciders, required amount, and capacity. The framework owns deficit search, the deficit-free state, ledger summation, fixed-priority comparison, residuals, typed execution, soundness, and totality.

## Workflow

1. Make a site one local location named by the proof and make its witnesses only the bounded evidence checked there.
2. Prove active and support deciders reflect the mathematical predicates.
3. Define contributions in the same additive codomain used by the manuscript inequality.
4. Run CT5 and prove the exact local-deficit, C4, charge-ledger, or aggregate terminal and trace.
5. Extract the typed residual rather than recomputing the deficit or sum in the application.

## Practicality and completion

Prove a polynomial work bound from the sum of local witness counts plus the ledger pass. Do not let a witness type range over ambient graphs, arbitrary subsets, or recursively generated proofs. If the generic machine lacks the reusable cost theorem needed by several examples, add that theorem to CT5 or `Core.WorkBudget` and keep the application lemma thin. Compile every terminal branch used by the proof and a small order-sensitive fixture.

## Absolute residual-carrier rule

Never define a node-local family, subtype, image, enumeration, chosen
representative collection, or replacement carrier. The CT may inspect only
collections already owned by the literal incoming residual and retrieved
from its single accumulated ledger. If access is missing, add a generic Core
projection/query of that same residual; do not manufacture application data.
