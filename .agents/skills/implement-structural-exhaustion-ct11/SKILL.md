---
name: implement-structural-exhaustion-ct11
description: Implement CT11 finite-sum localization in a structural-exhaustion Lean proof. Use for negative total budgets, admissibility gaps, a locally negative cell, degree-sum localization, or the reusable negative-budget profile.
---

# Implement Structural Exhaustion CT11

Use CT11 to turn a negative finite total into a concrete admissibility gap or locally negative budget cell.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT11") | {capability, capabilityProfiles, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT11/Automation.lean`, `NegativeBudget.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, `Examples/CT11AutomationFirst.lean`, `Graph/Mantel.lean`, and `examples/mantel`.

## Implement the author contract

Supply the cell type, admissibility predicate and decider, and local budget. Each invocation supplies its explicit finite cell collection, budget values, and negative-total proof. Prefer `CT11.NegativeBudgetProfile` when all cells are admissible.

The framework owns decomposition audit, admissibility scan, negative-budget localization, residuals, typed execution, soundness, and totality.

## Workflow

1. Choose cells as the local terms already occurring in the manuscript's finite sum.
2. Prove the global algebraic identity and strict negativity outside CT11.
3. Instantiate the profile or general capability without preselecting a negative cell.
4. Run CT11 and extract the typed admissibility-gap or localized-deficit residual.
5. Prove the exact terminal, trace, and local inequality used by the final contradiction.

## Practicality and completion

CT11 performs a finite scan over the supplied cells. Prove that collection size and each budget evaluation are polynomial in the input. Do not enumerate decompositions; supply the one mathematical decomposition proved by the source. Pin first negative cell order in a small fixture.

## Absolute residual-carrier rule

Never define a node-local family, subtype, image, enumeration, chosen
representative collection, or replacement carrier. The CT may inspect only
collections already owned by the literal incoming residual and retrieved
from its single accumulated ledger. If access is missing, add a generic Core
projection/query of that same residual; do not manufacture application data.
