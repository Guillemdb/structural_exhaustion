import Erdos64EG.Shared.CT10P13LabelAlgebra

namespace Erdos64EG.Internal.P13CurvatureArithmeticCertificate

open StructuralExhaustion

theorem crossOne_power_iff (left right : Fin 13) :
    PowerOfTwoLength
        (Graph.InducedPathAttachment.crossCycleLength 1 left right) ↔
      Graph.InducedPathAttachment.positionDistance left right = 1 ∨
        Graph.InducedPathAttachment.positionDistance left right = 5 := by
  decide +revert

theorem crossTwo_power_iff (left right : Fin 13) :
    PowerOfTwoLength
        (Graph.InducedPathAttachment.crossCycleLength 2 left right) ↔
      Graph.InducedPathAttachment.positionDistance left right = 0 ∨
        Graph.InducedPathAttachment.positionDistance left right = 4 ∨
        Graph.InducedPathAttachment.positionDistance left right = 12 := by
  decide +revert

end Erdos64EG.Internal.P13CurvatureArithmeticCertificate
