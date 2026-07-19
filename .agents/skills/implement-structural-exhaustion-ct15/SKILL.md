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
functional admissible quotient, use
`CT15.FunctionalAdmissibleRank.Profile.rankProfile` and its inherited
`Survives`/`targetRank`. Its candidate type contains exactly a carrier, raw
proposal, admissibility proof, and functional proof. Do not use
`CT15.AdmissibleQuotient.Profile.targetRank` alone: admission does not certify
the manuscript's realized quotient-image functional axiom. Do not identify an
exact-profile realization with a raw outside context or identify quotient-image
values with Boolean target responses unless an explicit semantic equivalence
theorem proves both directions. This proof-level maximum evaluates neither a
subfamily powerset nor a quotient family. Do not replace it with the count of
coordinates avoiding a pairwise identification predicate unless a theorem
proves the two rank notions equal.
Use `Profile.rankDecision` for the exact strict-loss/full-cardinality
dichotomy on that maximum. It is proof-level and has a zero-scan work budget;
do not run the coordinatewise CT15 interpreter merely to decide this rank
object.
Build every proof-level zero-scan certificate with
`Core.PolynomialCheckBudget.zero`; do not repeat the budget record in CT15
profiles or applications. A downstream node consumes the exact incoming stage
and full accumulated ledger through the framework node executor, retrieves the
CT15 decision through one `LedgerQuery`, and adds only its new semantic fact.
Never expose an exact-handoff or routing carrier in application code.
On a strict-loss edge, first check which quotient stage the manuscript uses.
`Profile.pairCircuitOfRankDrop` produces a circuit for an already
`Admissible` quotient.  Since `Admissible` includes context-universal response
and a represented reduction for every non-injective code, that circuit cannot
be used as the input of an earlier diamond which is supposed to decide target
defect, support location, or representative availability.  Doing so silently
preselects those edges and is a review failure.

When the paper localizes a determination, first compute rank over the exact
`FunctionalAdmissibleRank.Profile.Candidate` universe. Retain its
proof-selected connected boundaried support and declared support data, then
route the retained candidate through a proved collision-to-support-certificate
producer. `CT15.SupportStratifiedRank` may replace that universe only after an
all-and-only theorem proves code-cofinality in both directions; requiring a
complete support certificate for every collision at rank-definition time can
otherwise omit paper-admissible quotients. Then use
`Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate`.
Its `contextAudit` implements the actual defect/universal split, and its
`SupportLocation` implements the at-atom/enlarged split.  The at-atom universal
case executes the literal CT3 compression; the enlarged constructor is routed
unchanged.  The application must prove the certificate producer from the
preceding rank residual.  A universally quantified theorem accepting an
arbitrary certificate is conditional support, not a completed node.

Use `PairCircuit.ContextDecision`, `ContextDefect`,
`RepresentativeDecision`, and `smallerRepresentative` only when the
manuscript input is already an audited admissible quotient and no earlier
diagram edge asks to test the properties contained in admissibility.

## Workflow

1. Make coordinates the finite local rank components from the manuscript.
   For a centre-indexed fibre of unordered local pairs, use
   `Core.Enumeration.sigmaOrderedDistinctPairs`; use `finsetSubtype_card` and
   `finsetSubtype_sum_val_eq` when centres are owned by a `Finset`, and
   `subtype_card_eq_filter` for a predicate-selected fibre. Do not expose
   `Fintype.card_subtype` in the application.
2. Prove the target-dependence decider reflects the exact semantic predicate.
3. Define charge and capacity in the same units as the final inequality.
4. Run CT15 and prove the rank-drop, C4, or full-rank-ledger terminal and exact trace.
5. Extract the first coordinate or generated ledger from the typed outcome.

## Practicality and completion

Bound all work by a constant number of passes over local coordinates and polynomial-time charge evaluation. Do not make coordinates range over all target substructures. Test the first-hit rank drop and both full-rank comparison outcomes needed by the instance.
