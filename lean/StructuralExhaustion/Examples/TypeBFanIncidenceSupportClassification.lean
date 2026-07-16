import StructuralExhaustion.Graph.TypeBFanIncidenceSupportClassification

namespace StructuralExhaustion.Examples.TypeBFanIncidenceSupportClassification

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : TypeBFanShoulderIncidenceCoordinate.Profile object)
variable (assignedVertices windowVertices : Finset V)

open Graph.TypeBFanIncidenceSupportClassification

example (coordinate : Coordinate object profile) :
    (coordinate.endpoint object profile ∉ assignedVertices) ∨
      (coordinate.endpoint object profile ∈ assignedVertices ∧
        coordinate.shoulder object profile ∈ windowVertices) ∨
      (coordinate.endpoint object profile ∈ assignedVertices ∧
        coordinate.shoulder object profile ∉ windowVertices) :=
  coordinate.exhaustive object profile assignedVertices windowVertices

example (coordinate : Coordinate object profile) :
    object.graph.Adj (coordinate.endpoint object profile)
      (coordinate.shoulder object profile) :=
  coordinate.classified_incidence object profile

example : visibleChecks object profile ≤ 4 * object.input.vertices.card :=
  visibleChecks_linear object profile

example :
    (budget object profile).checks () ≤ (budget object profile).coefficient *
      ((budget object profile).size () + 1) ^ (budget object profile).degree :=
  (budget object profile).bounded ()

end StructuralExhaustion.Examples.TypeBFanIncidenceSupportClassification
