import StructuralExhaustion.Graph.TypeBFanCenterCoordinate

namespace StructuralExhaustion.Examples.TypeBFanCenterCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : Graph.TypeBFanCenterCoordinate.Profile object)

open Graph.TypeBFanCenterCoordinate

example (coordinate : Coordinate object profile) :
    object.graph.Adj profile.center (coordinate.endpoint object profile) :=
  coordinate.incident object profile

example (coordinate : Coordinate object profile) :
    4 ≤ object.degree profile.center :=
  coordinate.center_degree_ge_four object profile

example (coordinate : Coordinate object profile) :
    profile.center ∈ coordinate.support object profile ∧
      coordinate.endpoint object profile ∈ coordinate.support object profile :=
  ⟨coordinate.center_mem_support object profile,
    coordinate.endpoint_mem_support object profile⟩

example :
    (coordinates object profile).card = object.degree profile.center :=
  coordinates_card_eq_degree object profile

example : visibleChecks object profile ≤ object.input.vertices.card :=
  visibleChecks_linear object profile

example :
    (budget object profile).checks () ≤
      (budget object profile).coefficient *
        ((budget object profile).size () + 1) ^
          (budget object profile).degree :=
  (budget object profile).bounded ()

end StructuralExhaustion.Examples.TypeBFanCenterCoordinate
