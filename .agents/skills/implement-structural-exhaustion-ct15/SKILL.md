---
name: implement-structural-exhaustion-ct15
description: Implement CT15 target-relative rank and full-rank ledgers in a structural-exhaustion Lean proof. Use for finite rank coordinates, target dependence, first rank drops, charge ledgers, C4 certificates, or capacity residuals.
---

# Implement Structural Exhaustion CT15

Use CT15 to compute target-relative rank over explicit local coordinates, return the first drop, or compare the full-rank charge ledger with capacity.

## Read the current contract

```bash
jq '.tactics[] | select(.tacticId == "CT15") | {capability, nodes, terminals, residualKinds}' generated/lean-machines.json
```

Read `lean/StructuralExhaustion/CT15/Automation.lean`, `Spec.lean`, `Capability.lean`, `Execution.lean`, `Theorems.lean`, and `Examples/CT15AutomationFirst.lean` completely.

## Implement the author contract

Supply coordinate type, target-dependence predicate, charge and capacity functions, explicit coordinate `FinEnum`, and target-dependence decider. The framework owns rank contributions, computed rank, first-drop search, full-rank ledger entries and total, capacity comparison, residuals, C4 certificate, typed execution, soundness, and totality.

When the manuscript defines rank as the maximum subfamily surviving every
functional admissible quotient, first use
`CT15.AdmissibleQuotient.Profile.Survives` and `Profile.targetRank`. This exact
proof-level maximum evaluates neither a subfamily powerset nor a quotient
family. Do not replace it with the count of coordinates avoiding a pairwise
identification predicate unless a theorem proves the two rank notions equal.
Use `Profile.rankDecision` for the exact strict-loss/full-cardinality
dichotomy on that maximum. It is proof-level and has a zero-scan work budget;
do not run the coordinatewise CT15 interpreter merely to decide this rank
object.
Build every proof-level zero-scan certificate with
`Core.PolynomialCheckBudget.zero`; do not repeat the budget record in CT15
profiles or applications. When a downstream node retains a CT15 residual or
decision unchanged, extend `Core.ExactHandoff` and add only its new semantic
fields.
On the strict-loss edge, use `Profile.pairCircuitOfRankDrop` to retain an
actual admitted quotient, two distinct declared coordinates with equal code,
and the singleton functional basis. This is proof-selected from failure of
universal survival; never enumerate coordinate subfamilies or quotient
proposals to manufacture the circuit.
For the following outside-context validity node, use
`PairCircuit.ContextDecision` and `PairCircuit.contextDecision`.  An admitted
pair circuit projects `contextUniversal` directly from quotient admissibility,
retains the exact concrete-defect/universal decision type, proves
`noContextDefect`, and has the zero-check `contextDecisionBudget`.  Never scan
or materialize the context type to execute this diagram diamond.
On the defect terminal, retain the supplied witness with
`PairCircuit.ContextDefect`; use `toExists` for the manuscript's
target-defective payload and `impossible` to close that edge against the same
admitted quotient.  Do not search again for a distinguishing context.
For the representative decision, use `PairCircuit.proposal_not_injective`,
`smallerRepresentative`, and `RepresentativeDecision`.  Admission already
stores the `Core.CertifiedReduction`; project its strict decrease, baseline,
and target transport with the zero-check `representativeDecisionBudget`
instead of enumerating candidate representatives.

## Workflow

1. Make coordinates the finite local rank components from the manuscript.
2. Prove the target-dependence decider reflects the exact semantic predicate.
3. Define charge and capacity in the same units as the final inequality.
4. Run CT15 and prove the rank-drop, C4, or full-rank-ledger terminal and exact trace.
5. Extract the first coordinate or generated ledger from the typed outcome.

## Practicality and completion

Bound all work by a constant number of passes over local coordinates and polynomial-time charge evaluation. Do not make coordinates range over all target substructures. Test the first-hit rank drop and both full-rank comparison outcomes needed by the instance.
