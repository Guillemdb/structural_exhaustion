---
name: implement-structural-exhaustion-ct2
description: Implement CT2 minimal deletion or local replacement in a structural-exhaustion Lean proof. Use for explicit local deletion seeds, deletion criticality, bounded compatible-context tables, separating contexts, or criticality residuals.
---

# Implement Structural Exhaustion CT2

Use CT2 for the exact minimal-counterexample deletion or replacement step in the manuscript. Select one local piece first; never search over an ambient graph universe.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT2") | {capability, capabilityProfiles, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT2/Automation.lean`, `LocalDeletion.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT2AutomationFirst.lean`. Inspect `Graph/MinimumDegreeCycle.lean`, `Examples/CT2DeletionClosure.lean`, and the CT2 modules in `examples/even_cycle` and `examples/erdos_64_eg` for graph deletion.

## Choose the smallest contract

- Prefer `CT2.LocalDeletionCapability` when the manuscript supplies one explicit proper admissible piece and deletion alone yields the minimality contradiction. Supply the piece system, deletion operator, explicit seed, baseline preservation, and target monotonicity. Use the constant-one local run and its `notProper` theorem.
- Use `CT2.Capability.deletionOnly` when discovery must scan a small local piece enumerator but there are no replacement candidates.
- Use the full capability only when the proof genuinely compares a finite local candidate set across a finite local compatible-context set.

The full capability's author data are the piece, interface, context, observable, deletion, and replacement systems. The framework owns seed discovery, exact observations, candidate comparison, deletion and replacement C2 certificates, separating tables, residuals, paths, soundness, determinism, and totality.

## Implement rigorously

1. Work in one `MinimalCounterexampleContext`; use its inherited baseline, avoidance, rank, and minimality theorem.
2. Define pieces from immediate local structure such as a dart, bounded patch, or already selected subobject.
3. Make deletion return a `Core.SmallerObject` with an explicit rank-decrease proof.
4. For local deletion, prove preservation and monotonicity semantically without evaluating the target predicate.
5. For replacement, enumerate only legal replacements of the selected piece and only contexts compatible with its interface. Prove reconstruction and strict decrease.
6. Run the reference machine and prove the exact deletion C2, replacement C2, separating-context, or criticality terminal and trace.

## Practicality gate

Do not enumerate every subgraph, every graph interface, or every ambient context. The interface type need not be globally finite. Only pieces of the current object, contexts for the selected interface, and candidates for the selected piece may be enumerated. State and prove their polynomial check-count bound; use `localDeletionBudget` for the explicit deletion surface.

## Completion gate

If a residual feeds CT3 or CT10, use the registered route skill rather than embedding consumer data in CT2. Compile both enabled and disabled discovery cases when relevant. Leave no target decider in the local deletion path and no caller-authored outcome in the capability.

## Absolute residual-carrier rule

Never define a node-local family, subtype, image, enumeration, chosen
representative collection, or replacement carrier. The CT may inspect only
collections already owned by the literal incoming residual and retrieved
from its single accumulated ledger. If access is missing, add a generic Core
projection/query of that same residual; do not manufacture application data.
