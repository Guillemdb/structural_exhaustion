---
name: implement-hypostructure-ct15
description: Implement Hypostructure CT15 finite target-relative rank and full-rank charge ledgers. Use for residual-owned rank coordinates, first target-dependent coordinates, C4 overload certificates, capacity-fitting full-rank residuals, graph boundary-response coordinates, or PDE gauge, quotient, and active-coordinate rank toys.
---

# Implement Hypostructure CT15

Use the live CT15 contract to compute schedule-relative rank, find the first target-dependent coordinate, or build and compare the charge ledger when every scheduled coordinate is target-independent.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT15/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`;
- the applicable `Graph/CT15.lean` or `PDE/CT15.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT15.lean`;
- CT15 rows in `migration/hypostructure/api-feature-matrix.csv`, relevant PDE rows, route requirements, and barrel imports.

Do not infer richer rank machinery from older designs or mathematical prose. The live generic rank is exactly the sum of `rankContribution`, where a target-dependent scheduled coordinate contributes zero and every other coordinate contributes one; `targetRank` is the schedule cardinality.

If the proof requires a maximum over admissible quotients, functional realization, support-stratified rank, circuit extraction, or another stronger notion not present in the live modules, stop and use `$extend-hypostructure-framework`. Do not identify that notion with the finite count without a proved two-way equivalence. Apply the same hard gate to a `planned` or missing Graph/PDE or route layer; never emulate it in application-local code.

## Supply the finite rank primitives

Define `CT15.Spec` with predecessor-dependent `Coordinate`, primitive `TargetDependent`, coordinate `charge : ... -> Nat`, and total `capacity : Previous -> Nat`.

Define `CT15.Capability` with:

- the exact coordinate enumeration as `Core.Residual.Query`;
- a reflection-correct target-dependence decision;
- the polynomial input size, coefficient, degree, and bound.

Do not supply a rank, first drop, independence proof, full-rank state, charge ledger, C4 verdict, terminal, or trace. The schedule must be owned by the literal predecessor; no node-local pair family, subtype, quotient candidate list, or chosen support is allowed.

## Execute the rank audit

1. Choose coordinates that are exactly the finite local rank components justified by the manuscript.
2. Prove the target-dependence predicate has the intended semantics and units.
3. Define charge and capacity in the same units as the final comparison.
4. Prove `2 * coordinates.card + 1` fits the declared polynomial envelope.
5. Run `CT15.execute` or `ct15_execute`.
6. Consume the generated `RankState`, first-drop certificate, full-rank state, and ledger without recomputing them.

CT15 performs one complete rank pass. It then scans for the first target-dependent coordinate. Only on exhaustive independence does it build the ordered charge ledger and compare total charge with capacity.

## Discharge every outcome

Handle exactly:

- `.rankDrop`: computed rank and the first target-dependent coordinate with an independent prefix;
- `.c4`: exhaustive independence, literal full rank, exact ordered ledger, and `capacity < ledgerTotal`;
- `.fullRankLedger`: the same full-rank ledger with `ledgerTotal <= capacity`.

Prove predecessor equality, `OutcomeClaim`, exact trace, terminal exhaustiveness, totality, determinism, ledger-order preservation, and `checks_le_polynomial`. Give the rank-drop and capacity residuals typed downstream consumers. Do not expose a custom handoff or copy the ledger into application state.

## Use domain adapters with semantic proofs

- Graph: use `Graph.CT15.targetRelativeSpec` and `targetRelativeCapability`. The adapter evaluates supplied semantics against the queried `FiniteObject`; it does not define boundary rank or admissible quotient rank for you.
- PDE: use `PDE.CT15.targetRelativeSpec` and `targetRelativeCapability`. Gauge, cokernel, closed-range, quotient, and active-rank meanings remain obligations of the semantic inputs.

An adapter instance is sound only after the application proves its coordinates and `TargetDependent` predicate represent the manuscript rank. If that equivalence is missing, report a framework or mathematics gap rather than declaring CT15 complete.

## Validate completion

Keep `Fixtures/CT15.lean` covering the first-drop, C4, and full-rank-ledger terminals, first-hit order, exact rank and entries, traces, work, and both adapters. Run focused source and fixture checks, then package, import-firewall, and transitive axiom checks. Separate finite fixture success from theorem-level rank equivalence.
