import StructuralExhaustion.Graph.FiniteSupportRawCurvature

namespace StructuralExhaustion.Examples.FiniteSupportRawCurvature

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u v

variable {V : Type u} (object : FiniteObject V)
variable {Role : Type v} (roles : FinEnum Role) (active : Finset V)

example (coordinate :
    Graph.FiniteSupportRawCurvature.Coordinate (Role := Role) object active) :
    coordinate ∈
      (Graph.FiniteSupportRawCurvature.coordinates object roles active).orderedValues :=
  Graph.FiniteSupportRawCurvature.coordinate_mem object roles active coordinate

example : Graph.FiniteSupportRawCurvature.visibleChecks roles active ≤
    (2 + roles.card) * object.input.vertices.card ^ 3 :=
  Graph.FiniteSupportRawCurvature.visibleChecks_le_cubic object roles active

end StructuralExhaustion.Examples.FiniteSupportRawCurvature
