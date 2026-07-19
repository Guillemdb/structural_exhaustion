import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace StructuralExhaustion.Core

/-!
# Symbolic entropy of a finite type

This profile owns cardinality and normalized real entropy for a proof-level
finite carrier.  It deliberately carries no enumeration: clients may reason
about a finite subtype without constructing or scanning its values.
-/

universe u

namespace FiniteTypeEntropy

structure Profile where
  State : Type u
  finiteState : Finite State
  supportSize : Nat

attribute [instance] Profile.finiteState

namespace Profile

noncomputable def stateCount (profile : Profile) : Nat :=
  Nat.card profile.State

noncomputable def normalizedEntropy (profile : Profile) : ℝ :=
  Real.logb 2 profile.stateCount / profile.supportSize

@[simp] theorem normalizedEntropy_eq (profile : Profile) :
    profile.normalizedEntropy =
      Real.logb 2 profile.stateCount / profile.supportSize :=
  rfl

/-- The symbolic profile performs no primitive semantic checks. -/
def semanticChecks (_profile : Profile) : Nat := 0

@[simp] theorem semanticChecks_eq_zero (profile : Profile) :
    profile.semanticChecks = 0 :=
  rfl

end Profile

end FiniteTypeEntropy

end StructuralExhaustion.Core
