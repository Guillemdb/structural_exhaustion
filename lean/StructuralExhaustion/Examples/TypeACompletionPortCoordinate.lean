import StructuralExhaustion.Graph.TypeACompletionPortCoordinate

namespace StructuralExhaustion.Examples.TypeACompletionPortCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph
open Graph.TypeACompletionPortCoordinate

universe u

variable {V : Type u} (object : FiniteObject V)
variable
  (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)

/-! A non-Erdős consumer of the exact completion-port schedule. -/

example (port : Coordinate object profile) :
    (profile.supportObject object).degree
      (port.receiver object profile) ≤ 2 :=
  port.receiver_internal_degree_le_two object profile

example (port : Coordinate object profile) :
    object.degree (port.receiver object profile).1 = 3 :=
  port.receiver_ambient_degree_eq_three object profile

example (port : Coordinate object profile) :
    object.graph.Adj (port.receiver object profile).1
        (port.outside object profile) ∧
      port.outside object profile ∉ profile.support :=
  ⟨port.adjacent object profile,
    port.outside_not_mem_support object profile⟩

example :
    (coordinates object profile).card ≤ 3 * profile.support.card :=
  coordinates_card_le_three_mul_support object profile

example :
    visibleChecks object profile ≤ 4 * object.input.vertices.card :=
  visibleChecks_polynomial object profile

example :
    (budget object profile).checks () ≤
      (budget object profile).coefficient *
        ((budget object profile).size () + 1) ^
          (budget object profile).degree :=
  (budget object profile).bounded ()

end StructuralExhaustion.Examples.TypeACompletionPortCoordinate
