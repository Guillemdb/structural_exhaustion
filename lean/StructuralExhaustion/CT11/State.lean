import StructuralExhaustion.CT11.Capability

namespace StructuralExhaustion.CT11

universe uAmbient uBranch uCell
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uCell} P)
variable (input : Input capability)

structure AdmissibilityGapResidual where
  cell : capability.Cell
  member : cell ∈ input.cells.values
  inadmissible : ¬ capability.Admissible input.context cell

structure AdmissibleDecomposition : Prop where
  admissible : ∀ cell : capability.Cell, cell ∈ input.cells.values →
    capability.Admissible input.context cell

structure LocalizedDeficitResidual where
  admissible : AdmissibleDecomposition capability input
  cell : capability.Cell
  member : cell ∈ input.cells.values
  negative : capability.localBudget input.context cell < 0

end StructuralExhaustion.CT11
