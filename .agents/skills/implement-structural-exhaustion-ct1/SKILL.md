---
name: implement-structural-exhaustion-ct1
description: Implement CT1 finite target realization in a structural-exhaustion Lean proof. Use for explicit target certificates, polynomial finite realization searches, public-target bridges, C1 runs, or target-avoiding residuals.
---

# Implement Structural Exhaustion CT1

Use CT1 to validate an explicit target witness or exhaust a genuinely local finite realization space. Do not turn CT1 into an enumeration of ambient graphs.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT1") | {capability, capabilityProfiles, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT1/Automation.lean`, `Capability.lean`, `TargetEncoding.lean`, `Theorems.lean`, and `Examples/CT1AutomationFirst.lean` completely. For graph certificates, also inspect `Graph/CycleCertificate.lean`, `Graph/Coloring.lean`, and the CT1 modules in the external examples.

## Choose the execution surface

- Use `CT1.TargetCertificateEncoding` when the proof already constructs an accepted code. Supply `Code`, `Accepts`, `encode`, and `decode`, then call its direct proof-carrying runner.
- Use `CT1.TargetEncoding` only when discovery is required and the code enumerator has a proved polynomial bound.
- Use raw `CT1.Spec` and `CT1.Capability` only for a target with multiple test indices or dependent witness families not captured by the one-code profiles.

For the raw capability, supply exactly the test type, dependent witnesses, realization predicate, explicit test and witness `FinEnum` values, realization decider, input size, coefficient, degree, and `workBound`. The framework owns equivalence certification, dependent search, C1 construction, avoidance, typed paths, soundness, and totality.

## Implement rigorously

1. Define the code as the mathematical certificate from the source proof: for example, a walk with cycle proofs, a coloring with properness, or another local witness.
2. Make `Accepts` check only the certificate fields needed by the target.
3. Prove `decode` directly into the public theorem predicate and prove `encode` from any supplied public-target witness.
4. If using finite search, expose the exact enumerator order and prove its length is bounded by the declared polynomial.
5. Run CT1 through the public evidence-carrying API. Retain the terminal, outcome, and typed path together.
6. Prove the expected `.c1` or `.avoiding` terminal, semantic claim, exact trace, totality, and check budget.

## Practicality gate

Reject witness types such as all `SimpleGraph V`, all subgraphs, all color functions, or all arbitrary walks. Prefer a certificate supplied by an earlier constructive step. A finite search is acceptable only when its enumerator is proof-specified, local, and polynomial in the declared input size.

## Completion gate

Expose the public-target bridge when the theorem uses an independently named predicate. Add a small accepted and avoiding fixture where both branches are relevant. Compile the application package and run the architecture linter; do not supply a completed C1 certificate as a capability field.
