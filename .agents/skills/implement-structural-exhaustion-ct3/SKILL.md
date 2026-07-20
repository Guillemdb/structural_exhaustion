---
name: implement-structural-exhaustion-ct3
description: Implement CT3 exact local-response compression in a structural-exhaustion Lean proof. Use for boundaried pieces, compatible glued contexts, finite response coordinates, smaller representatives, known rows, or distinguishing coordinates.
---

# Implement Structural Exhaustion CT3

Use CT3 to compare pieces through the finite local observations named by the proof. The target is related to each response bit by a theorem; CT3 never decides the target over a generated ambient universe.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT3") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT3/Automation.lean`, `Capability.lean`, `TargetCompression.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT3AutomationFirst.lean`. Use `examples/even_cycle/EvenCycleExample/CT3SeriesReduction.lean` as the complete independent instantiation and `examples/erdos_64_eg/Erdos64EG/CT3.lean` as the graph-target specialization.

## Implement the local-coordinate contract

Prefer `CT3.TargetCompressionContract`. Supply:

- piece, compatible-context, coordinate, candidate, and row types;
- `glue`, `classify`, and the Boolean local `response`;
- `response_correct` for every piece and compatible context;
- candidate pieces, admissibility, and strict-smaller semantics;
- row representatives and stored responses;
- explicit coordinate, candidate, and row `FinEnum` values and primitive deciders; and
- input size, coefficient, degree, and the polynomial `workBound`.

The framework owns and derives the raw spec and capability, exact vectors, first compression, table validation, exact-row lookup, audited run, typed path, soundness, totality, and response-based target transport.

## Implement rigorously

1. Take coordinates directly from the finite tests in the manuscript, not from all ambient contexts.
2. Define `classify` so every compatible semantic context maps to one coordinate.
3. Prove `response_correct : response piece (classify context) = true ↔ Target (glue piece context)` without a global target decider.
4. Define candidates as the actual smaller representatives permitted by the proof and rows as its canonical finite response table.
5. Prove `localCheckBound coordinates candidates rows` is polynomial in the declared input size.
6. Run the audited contract and prove the expected compression, distinguishing-context, known-row, or novel-row terminal and typed trace.
7. Use `sameResponse_target_iff` or `sameResponse_targetIncluded` to transport the target through response equality.

## Practicality gate

Keep coordinates, candidates, and rows small and proof-specified. Do not materialize a universe of boundaried graphs or recursively generate contexts. The exact worst-case schedule is
`candidates * (2 + coordinates) + 2 * rows * coordinates`; choose data for which this is practical and prove the bound.

## Completion gate

Test every response coordinate, every canonical row, and each intended representative. Pin the exact `checkLimit`, terminal, trace, semantic soundness, and target-preservation theorem. Do not replace the universal contract with a fixture or claim later manuscript stages.

## Absolute residual-carrier rule

Never define a node-local family, subtype, image, enumeration, chosen
representative collection, or replacement carrier. The CT may inspect only
collections already owned by the literal incoming residual and retrieved
from its single accumulated ledger. If access is missing, add a generic Core
projection/query of that same residual; do not manufacture application data.
