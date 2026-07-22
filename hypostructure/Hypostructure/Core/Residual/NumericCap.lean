import Hypostructure.Core.Residual.Focus

/-!
# Focused numeric-cap split

This module provides a domain-neutral focused binary split over two
predecessor-owned natural-number quantities.  Applications provide the
quantities through active ledger queries.  Core performs the comparison,
records the exact branch evidence in the focused extension, derives the
successor focus, and accounts for the one comparison check.
-/

namespace Hypostructure.Core.Residual.NumericCap

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uPrevious

/-- Minimal public contract for a focused natural-number cap decision.
The domain supplies only predecessor-owned quantities and the size function
used by the generic constant-work envelope. -/
structure Contract {Previous : Sort uPrevious}
    (profile : Focus.Profile Previous) where
  load : Focus.ActiveQuery profile fun _previous _active => Nat
  cap : Focus.ActiveQuery profile fun _previous _active => Nat
  size : Previous -> Nat

namespace Contract

variable {Previous : Sort uPrevious} {profile : Focus.Profile Previous}
variable (contract : Contract profile)

/-- The selected active predecessor is within the registered cap. -/
def Within (previous : Previous) (active : profile.Active previous) : Prop :=
  contract.load.read previous active <= contract.cap.read previous active

/-- The complementary residual selected when the cap is exceeded. -/
def Exceeds (previous : Previous) (active : profile.Active previous) : Prop :=
  Not (contract.Within previous active)

/-- Core-owned outcome of the cap comparison. -/
inductive Outcome (previous : Previous) (active : profile.Active previous) where
  | within (proof : contract.Within previous active) :
      Outcome previous active
  | exceeds (proof : contract.Exceeds previous active) :
      Outcome previous active

/-- One focused extension storing only the framework-owned comparison
certificate. -/
abbrev Stage :=
  Focus.Stage profile fun previous active => contract.Outcome previous active

/-- Exact local work for the comparison on an already-active predecessor. -/
def comparisonBudget : PolynomialCheckBudget Previous :=
  PolynomialCheckBudget.constant contract.size 1

/-- Polynomial envelope for the focused selector followed by the cap
comparison. -/
def workBudget : PolynomialCheckBudget Previous :=
  profile.selectionBudget.add contract.comparisonBudget

/-- Counted comparison payload. -/
def decideCounted (previous : Previous) (active : profile.Active previous)
    (_selectionChecks : Nat)
    (_exact : _selectionChecks = profile.selectionBudget.checks previous) :
    Counted (contract.Outcome previous active) :=
  if proof :
      contract.load.read previous active <=
        contract.cap.read previous active then
    ⟨.within (by
      unfold Within
      exact proof), 1⟩
  else
    ⟨.exceeds (by
      unfold Exceeds Within
      exact proof), 1⟩

@[simp] theorem decideCounted_checks (previous : Previous)
    (active : profile.Active previous) (selectionChecks : Nat)
    (exact : selectionChecks = profile.selectionBudget.checks previous) :
    (contract.decideCounted previous active selectionChecks exact).checks =
      contract.comparisonBudget.checks previous := by
  unfold decideCounted comparisonBudget
  by_cases h :
      contract.load.read previous active <=
        contract.cap.read previous active <;>
    simp [h, PolynomialCheckBudget.constant]

/-- Execute the cap split over the literal predecessor.  Inactive siblings
receive only the existing focused inactive marker. -/
def runCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCountedPayload profile contract.comparisonBudget previous
    (contract.decideCounted previous)
    (fun active selectionChecks exact =>
      contract.decideCounted_checks previous active selectionChecks exact)

/-- Uncounted stage produced by `runCounted`. -/
def run (previous : Previous) : contract.Stage :=
  (contract.runCounted previous).value

@[simp] theorem runCounted_previous (previous : Previous) :
    (contract.runCounted previous).value.previous = previous :=
  Focus.runCountedPayload_previous profile contract.comparisonBudget previous
    (contract.decideCounted previous)
    (fun active selectionChecks exact =>
      contract.decideCounted_checks previous active selectionChecks exact)

@[simp] theorem run_previous (previous : Previous) :
    (contract.run previous).previous = previous :=
  contract.runCounted_previous previous

/-- Active predecessors pay the selector plus exactly one comparison. -/
theorem runCounted_checks_of_active (previous : Previous)
    (active : profile.Active previous) :
    (contract.runCounted previous).checks =
      contract.workBudget.checks previous :=
  Focus.runCountedPayload_checks_of_active profile
    contract.comparisonBudget previous
    (contract.decideCounted previous)
    (fun active selectionChecks exact =>
      contract.decideCounted_checks previous active selectionChecks exact)
    active

/-- Inactive predecessors skip the cap comparison. -/
theorem runCounted_checks_of_inactive (previous : Previous)
    (inactive : Not (profile.Active previous)) :
    (contract.runCounted previous).checks =
      profile.selectionBudget.checks previous :=
  Focus.runCountedPayload_checks_of_inactive profile
    contract.comparisonBudget previous
    (contract.decideCounted previous)
    (fun active selectionChecks exact =>
      contract.decideCounted_checks previous active selectionChecks exact)
    inactive

/-- Every branch is bounded by the generic selector-plus-comparison
polynomial envelope. -/
theorem runCounted_checks_bounded (previous : Previous) :
    (contract.runCounted previous).checks <=
      contract.workBudget.coefficient *
        (contract.workBudget.size previous + 1) ^
          contract.workBudget.degree :=
  Focus.runCountedPayload_checks_bounded profile
    contract.comparisonBudget previous
    (contract.decideCounted previous)
    (fun active selectionChecks exact =>
      contract.decideCounted_checks previous active selectionChecks exact)

/-- The framework-owned successor focus after one cap decision. -/
abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor profile fun previous active =>
    contract.Outcome previous active

/-- Query the comparison outcome installed by the latest focused extension. -/
def outcomeQuery :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.Outcome stage.previous active :=
  Focus.ActiveQuery.latest

/-- Refine the successor focus to the within-cap branch. -/
def withinRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      match contract.outcomeQuery.read stage active with
      | .within _proof => True
      | .exceeds _proof => False)
    (fun stage active =>
      match contract.outcomeQuery.read stage active with
      | .within _proof => ⟨.isTrue trivial, 1⟩
      | .exceeds _proof => ⟨.isFalse (by intro h; exact h), 1⟩)
    (PolynomialCheckBudget.constant (fun _stage => 0) 1)
    (fun stage active => by
      cases contract.outcomeQuery.read stage active <;> rfl)

/-- Refine the successor focus to the exceeded-cap branch. -/
def exceedsRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      match contract.outcomeQuery.read stage active with
      | .within _proof => False
      | .exceeds _proof => True)
    (fun stage active =>
      match contract.outcomeQuery.read stage active with
      | .within _proof => ⟨.isFalse (by intro h; exact h), 1⟩
      | .exceeds _proof => ⟨.isTrue trivial, 1⟩)
    (PolynomialCheckBudget.constant (fun _stage => 0) 1)
    (fun stage active => by
      cases contract.outcomeQuery.read stage active <;> rfl)

/-- Focus containing exactly the live within-cap successor branch. -/
abbrev withinFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.withinRefinement

/-- Focus containing exactly the live exceeded-cap successor branch. -/
abbrev exceedsFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.exceedsRefinement

/-- Retrieve the exact within-cap certificate selected by the derived
within branch. -/
def withinProofQuery :
    Focus.ActiveQuery contract.withinFocus fun stage active =>
      contract.Within stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    cases outcome : contract.outcomeQuery.read stage active.parent with
    | within proof => exact proof
    | exceeds _proof =>
        have selected := active.accepted
        simp [withinRefinement, Focus.Refinement.ofDecision, outcome] at selected

/-- Retrieve the exact exceeded-cap certificate selected by the derived
exceeded branch. -/
def exceedsProofQuery :
    Focus.ActiveQuery contract.exceedsFocus fun stage active =>
      contract.Exceeds stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    cases outcome : contract.outcomeQuery.read stage active.parent with
    | within _proof =>
        have selected := active.accepted
        simp [exceedsRefinement, Focus.Refinement.ofDecision, outcome] at selected
    | exceeds proof => exact proof

end Contract

end Hypostructure.Core.Residual.NumericCap
