import Mathlib.Combinatorics.SimpleGraph.Finite
import StructuralExhaustion.Core.FiniteTypeEntropy

namespace StructuralExhaustion.Graph

open StructuralExhaustion

/-!
# Predicate-defined finite labelled-graph families

The graph layer owns the finite carrier of all labelled simple graphs
satisfying a supplied mathematical predicate.  `State` is a subtype and its
cardinality is symbolic; no graph universe is enumerated or executed.
-/

universe u

namespace ConstrainedLabelledGraphFamily

structure Profile (V : Type u) [Fintype V] [DecidableEq V] where
  admissible : SimpleGraph V → Prop
  supportSize : Nat

namespace Profile

variable {V : Type u} [Fintype V] [DecidableEq V]

def State (profile : Profile V) :=
  { graph : SimpleGraph V // profile.admissible graph }

noncomputable instance (profile : Profile V) : Finite profile.State := by
  classical
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable def entropyProfile (profile : Profile V) :
    Core.FiniteTypeEntropy.Profile where
  State := profile.State
  finiteState := inferInstance
  supportSize := profile.supportSize

noncomputable def stateCount (profile : Profile V) : Nat :=
  profile.entropyProfile.stateCount

noncomputable def normalizedEntropy (profile : Profile V) : ℝ :=
  profile.entropyProfile.normalizedEntropy

@[simp] theorem normalizedEntropy_eq (profile : Profile V) :
    profile.normalizedEntropy =
      Real.logb 2 profile.stateCount / profile.supportSize :=
  rfl

@[simp] theorem semanticChecks_eq_zero (profile : Profile V) :
    profile.entropyProfile.semanticChecks = 0 :=
  rfl

end Profile

end ConstrainedLabelledGraphFamily

end StructuralExhaustion.Graph
