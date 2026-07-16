import StructuralExhaustion.Graph.TypeBFanShoulderIncidenceCoordinate

namespace StructuralExhaustion.Examples.TypeBFanShoulderIncidenceCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : Graph.TypeBFanShoulderIncidenceCoordinate.Profile object)

open Graph.TypeBFanShoulderIncidenceCoordinate

example (coordinate : Coordinate object profile) :
    object.graph.Adj profile.center (coordinate.endpoint object profile) ∧
      object.graph.Adj (coordinate.endpoint object profile)
        (coordinate.shoulder object profile) :=
  ⟨coordinate.center_incident object profile,
    coordinate.shoulder_incident object profile⟩

example (coordinate : Coordinate object profile) :
    object.degree (coordinate.endpoint object profile) = 3 :=
  coordinate.endpoint_cubic object profile

example (coordinate : Coordinate object profile) :
    coordinate.shoulder object profile ≠ profile.center :=
  coordinate.shoulder_ne_center object profile

example :
    (coordinates object profile).card = 2 * object.degree profile.center :=
  coordinates_card_eq_two_mul_degree object profile

example : visibleChecks object profile ≤ 2 * object.input.vertices.card :=
  visibleChecks_linear object profile

example :
    (budget object profile).checks () ≤
      (budget object profile).coefficient *
        ((budget object profile).size () + 1) ^
          (budget object profile).degree :=
  (budget object profile).bounded ()

end StructuralExhaustion.Examples.TypeBFanShoulderIncidenceCoordinate
