import Mathlib.Analysis.SpecialFunctions.Log.Base
import StructuralExhaustion.Core.OrderThresholdSplit

namespace StructuralExhaustion.Examples.OrderThresholdSplit

open StructuralExhaustion

noncomputable def realProfile : Core.OrderThresholdSplit.Profile ℝ where
  value := Real.logb 2 8
  threshold := 3

example : realProfile.threshold ≤ realProfile.value ∨
    realProfile.value < realProfile.threshold :=
  realProfile.exhaustive

example : realProfile.workBudget.checks () = 0 :=
  realProfile.checks_eq_zero

/-! The accumulated-stage interface is exercised independently of any
problem-specific graph development. -/

abbrev FixtureResidual := Nat

abbrev FixturePrevious (_residual : FixtureResidual) := Nat

def dependentNatFamily :
    Core.OrderThresholdSplit.DependentProfileFamily
      FixtureResidual FixturePrevious Nat where
  profile := fun residual previous =>
    { value := previous
      threshold := residual }

abbrev FixtureDecision (residual : FixtureResidual) :=
  dependentNatFamily.Decision residual

abbrev FixtureStrictDecision (residual : FixtureResidual) :=
  dependentNatFamily.StrictDecision residual

noncomputable def dependentNatNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixturePrevious) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) FixtureDecision :=
  dependentNatFamily.executeUsingStage

noncomputable def dependentNatStrictNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FixturePrevious) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      FixtureStrictDecision :=
  dependentNatFamily.executeStrictUsingStage

theorem dependentNatFamily_total (residual previous : Nat) :
    dependentNatFamily.High residual previous ∨
      dependentNatFamily.Low residual previous :=
  dependentNatFamily.exhaustive previous

theorem dependentNatFamily_strict_total (residual previous : Nat) :
    dependentNatFamily.StrictHigh residual previous ∨
      dependentNatFamily.AtMost residual previous :=
  dependentNatFamily.strictExhaustive previous

theorem dependentNatFamily_zero_work :
    dependentNatFamily.workBudget.checks () = 0 :=
  dependentNatFamily.checks_eq_zero

end StructuralExhaustion.Examples.OrderThresholdSplit
