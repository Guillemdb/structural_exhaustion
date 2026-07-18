import StructuralExhaustion.Graph.TypeAReceiverSaturation

namespace StructuralExhaustion.Examples.TypeAReceiverSaturation

open StructuralExhaustion

universe u

variable {V : Type u} (object : Graph.FiniteObject V)
variable (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)

example :
    match Graph.TypeAReceiverSaturation.run object profile with
    | .found hit =>
        Graph.TypeAReceiverSaturation.Saturated object profile hit.value
    | .absent _ =>
        ∀ receiver : Graph.TypeAReceiverSaturation.Receiver object profile,
          ¬Graph.TypeAReceiverSaturation.Saturated object profile receiver :=
  Graph.TypeAReceiverSaturation.run_total object profile

example : Graph.TypeAReceiverSaturation.checks object profile ≤
    object.input.vertices.card ^ 2 :=
  Graph.TypeAReceiverSaturation.checks_quadratic object profile

end StructuralExhaustion.Examples.TypeAReceiverSaturation
