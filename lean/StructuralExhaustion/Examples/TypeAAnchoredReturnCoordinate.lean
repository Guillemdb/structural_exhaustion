import StructuralExhaustion.Graph.TypeAAnchoredReturnCoordinate

namespace StructuralExhaustion.Examples.TypeAAnchoredReturnCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable
  (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)
  (producer : Graph.TypeAAnchoredReturnCoordinate.Producer object profile)

open Graph.TypeAAnchoredReturnCoordinate

noncomputable example (port : Port object profile) :
    AnchoredReturn object profile port :=
  producer.produce object profile port

example (port : Port object profile) :
    let anchored := producer.produce object profile port
    (anchored.path object profile).IsPath := by
  let anchored := producer.produce object profile port
  exact anchored.isPath object profile

example : additionalChecks = 0 := additionalChecks_eq_zero

end StructuralExhaustion.Examples.TypeAAnchoredReturnCoordinate
