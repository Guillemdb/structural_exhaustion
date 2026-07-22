import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Hypostructure.Core.FiniteEntropy

universe u

/-! A symbolic entropy profile.  The finite carrier is supplied by a contract;
the framework derives its cardinality and normalized entropy. -/

structure Profile where
  State : Type u
  finiteState : Finite State
  supportSize : Nat

attribute [instance] Profile.finiteState

namespace Profile

noncomputable def stateCount (profile : Profile) : Nat := Nat.card profile.State

noncomputable def normalized (profile : Profile) : ℝ :=
  Real.logb 2 profile.stateCount / profile.supportSize

def semanticChecks (_profile : Profile) : Nat := 0

@[simp] theorem semanticChecks_eq_zero (profile : Profile) :
    profile.semanticChecks = 0 := rfl

end Profile

end Hypostructure.Core.FiniteEntropy
