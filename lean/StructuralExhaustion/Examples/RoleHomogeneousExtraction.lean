import StructuralExhaustion.Graph.RoleHomogeneousExtraction

namespace StructuralExhaustion.Examples.RoleHomogeneousExtraction

open StructuralExhaustion
open StructuralExhaustion.Graph

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def items : Core.OrderedCollection (Fin 37) where
  values := (inferInstance : FinEnum (Fin 37)).orderedValues
  nodup := (inferInstance : FinEnum (Fin 37)).nodup_orderedValues
  decEq := inferInstance

def constantRole (_ : Fin 37) : SurplusTokenRole.Role :=
  (.overlap, .primitiveVertex)

/-- A 37-edge textbook monochromatic pattern exceeds the 36-role capacity
at threshold two. -/
example : ∃ role : SurplusTokenRole.Role,
    2 ≤ CT9.fibreCount
      (RoleHomogeneousExtraction.capability problem (Fin 37) constantRole)
      (RoleHomogeneousExtraction.input context items) role := by
  apply RoleHomogeneousExtraction.exists_role_fibre_of_overload
  native_decide

end StructuralExhaustion.Examples.RoleHomogeneousExtraction
