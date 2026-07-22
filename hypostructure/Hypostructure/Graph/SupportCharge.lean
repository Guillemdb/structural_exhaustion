import Hypostructure.Graph.Finite
import Hypostructure.Core.SupportSplit

namespace Hypostructure.Graph.SupportCharge

universe u

/-! Graph projection of support charge.  The signed support schedule is the
Core contract; this module only derives degree-based graph observables.
Connectivity is supplied separately by the connected-support adapter. -/

abbrev Parameters := Hypostructure.Core.SupportSplit.Parameters

/-! The support schedule and signed charge are Core-owned.  The object
parameter is retained in this adapter's public name for source compatibility;
graph-specific meaning enters only through the degree projection below. -/
abbrev Support (_object : FiniteObject) (Cell : Type u) :=
  Hypostructure.Core.SupportSplit.Source Cell

def highCenters (object : FiniteObject) (threshold : Nat)
    (core : Finset object.Vertex) : Finset object.Vertex := by
  letI := object.vertices.decEq
  exact core.filter fun vertex => threshold ≤ object.degree vertex

structure High (object : FiniteObject) (threshold : Nat)
    (core : Finset object.Vertex) where
  center : object.Vertex
  center_mem : center ∈ core
  threshold_le : threshold ≤ object.degree center

structure Low (object : FiniteObject) (threshold : Nat)
    (core : Finset object.Vertex) where
  noHigh : highCenters object threshold core = ∅

noncomputable def highWitness {object : FiniteObject} {threshold : Nat}
    {core : Finset object.Vertex} (high : (highCenters object threshold core).Nonempty) :
    High object threshold core := by
  classical
  let member := high.choose_spec
  have filtered := Finset.mem_filter.mp member
  exact ⟨high.choose, filtered.1, filtered.2⟩

theorem low_of_not_high {object : FiniteObject} {threshold : Nat}
    {core : Finset object.Vertex}
    (not_high : ¬ (highCenters object threshold core).Nonempty) :
    Low object threshold core := by
  exact ⟨Finset.not_nonempty_iff_eq_empty.mp not_high⟩

theorem high_or_low (object : FiniteObject) (threshold : Nat)
    (core : Finset object.Vertex) :
    (highCenters object threshold core).Nonempty ∨
      (highCenters object threshold core = ∅) := by
  rcases Finset.eq_empty_or_nonempty (highCenters object threshold core) with
    empty | nonempty
  · exact Or.inr empty
  · exact Or.inl nonempty

end Hypostructure.Graph.SupportCharge
