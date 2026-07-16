import StructuralExhaustion.Graph.InducedPathComponentHighCenterSplit

namespace StructuralExhaustion.Examples.InducedPathComponentHighCenterSplit

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (componentInput : InducedPathComponentBoundarySchedule.Input object)
variable (minimumDegreeThree : 3 ≤ object.minDegree)

example :
    (∃ high, InducedPathComponentHighCenterSplit.run object componentInput
      minimumDegreeThree = .high high) ∨
    (∃ noHigh, InducedPathComponentHighCenterSplit.run object componentInput
      minimumDegreeThree = .noHigh noHigh) := by
  cases equation : InducedPathComponentHighCenterSplit.run object componentInput
      minimumDegreeThree with
  | high output => exact Or.inl ⟨output, rfl⟩
  | noHigh output => exact Or.inr ⟨output, rfl⟩

example : InducedPathComponentHighCenterSplit.visibleChecks object componentInput ≤
    object.input.vertices.card :=
  InducedPathComponentHighCenterSplit.visibleChecks_linear object componentInput

end StructuralExhaustion.Examples.InducedPathComponentHighCenterSplit
