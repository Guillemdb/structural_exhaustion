---
name: implement-hypostructure-ct2
description: Implement Hypostructure CT2 residual-selected local deletion and criticality. Use for minimal-counterexample deletion of one exact local piece, strict progress, deletion-C2 closure, graph edge deletion, or the complementary criticality residual.
---

# Implement Hypostructure CT2

Use the live CT2 profile for one local piece selected by the predecessor, followed by deletion or criticality. Do not search an ambient object universe.

## Gate the live contract

1. Read row `ct.ct2` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT2/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`.
3. Inspect `hypostructure/Hypostructure/Graph/CT2.lean` and `hypostructure/Hypostructure/Fixtures/CT2.lean`.
4. Confirm a fresh `.olean` with a focused check such as `cd hypostructure && lake env lean Hypostructure/Fixtures/CT2.lean`. Do not infer availability from filenames or the matrix alone.

The current kernel-checked vertical slice is residual-selected local deletion. `Automation.lean` explicitly omits bounded replacement, and no `Hypostructure/PDE/CT2.lean` adapter currently exists. Recheck live source before acting.

If the proof needs replacement candidates, compatible contexts, a PDE constructor, or another absent branch, forbid application-local emulation. Send that work to `$extend-hypostructure-framework`; require a complete Capability-to-Automation slice and complementary fixtures before using it.

## Author only the local mathematics

Define `CT2.Spec` with `Piece`, `Proper`, `Admissible`, and `delete`. Define `CT2.Capability` with exactly:

- a `Core.Residual.Query` for the inherited `Core.MinimalCounterexampleContext`;
- a `Core.Residual.Query` for the exact finite pieces of that context's object;
- a `Core.Residual.Query` for the selected bounded index;
- primitive properness and admissibility deciders;
- strict progress of the selected deletion;
- baseline preservation; and
- target monotonicity back to the original object.

Do not pass a selected piece directly. `Capability.selectedPiece` must derive it from `pieces` and `selectedIndex`. The current verifier budget is the framework-owned constant-one `localDeletionBudget`; do not add an application-authored work counter.

Record semantic operations and laws as author primitives, the three typed reads as inferred predecessor dependencies, and selection, eligibility decision, typed outcome, witness or criticality state, route, trace, and accumulated stage as framework outputs in `Core.Provision` metadata.

## Run the exact dichotomy

1. Execute `CT2.execute capability previous` on the literal accumulated predecessor.
2. Let Core select `.deletionC2` or `.criticality`; never construct a terminal or `CriticalityState` in the application.
3. Treat an eligible deletion as a mandatory minimality closure. Use `DeletionRun`/`closeSelected` and its contradiction and exact deletion-C2 trace; do not expose the impossible positive branch as an application remainder.
4. Consume criticality through `result.criticality`, `notProper_of_admissible`, or `notAdmissible_of_proper` as appropriate.
5. Prove predecessor retention, semantic soundness with `verified`, exact trace with `trace_exact`, `checks_eq_one`, `checks_le_polynomial`, `run_total`, determinism, and terminal exhaustiveness.

For graphs, use `Graph.CT2.edgeDeletionSpec` and `edgeDeletionCapability`; let Graph prove certified-edge properness and lexicographic decrease while the application supplies only admissibility, preservation, target monotonicity, and the three predecessor queries. Use `selectedEdge_mem` and `selectedEdge_notAdmissible` instead of redoing selection or criticality.

Use `Fixtures/CT2.lean` as the acceptance pattern: test both local eligibility failures, mandatory deletion closure, literal residual preservation, one-check tracing, and residual-selected graph edge deletion.

## Residual and locality rules

Select only a piece already present in the incoming residual. Never create a detached subgraph family, candidate list, replacement carrier, or node-local selected subtype. A missing ledger view is a Core/domain abstraction gap, not permission to rebuild the carrier in the application.
