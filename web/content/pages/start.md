# Implement a problem

This guide follows the shortest path from a mathematical target to an executable Hypostructure proof.

## 1. Register the problem and target

Define a `Core.Problem` with an ambient object, baseline predicate, and branch state. Keep the target separate so the same ambient model can support several theorems.

## 2. Create the root residual

Choose one stable residual carrier containing the problem instance and irreducible hypotheses. Initialize its `Core.Residual.Ledger` exactly once.

## 3. Choose a CT

Select the CT whose computed alternatives match the mathematics. Supply its `Spec` and the smallest capability needed to execute it; do not construct a terminal or successor stage by hand.

## 4. Run and query

Call the CT executor on the literal predecessor. Retrieve inherited facts with typed ledger queries, and focus a branch only through Core's decision and focus APIs.

## 5. Route or close

Use a registered typed transition to advance the complete ledger. Close a branch only from the framework result that carries the required terminal evidence.

## 6. Verify work and trust

Exercise every outcome with a focused fixture, prove the advertised work bound, and audit public endpoints with `#print axioms`.
