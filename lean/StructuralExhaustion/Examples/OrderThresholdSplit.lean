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

end StructuralExhaustion.Examples.OrderThresholdSplit
