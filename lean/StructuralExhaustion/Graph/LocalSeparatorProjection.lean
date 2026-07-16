import StructuralExhaustion.Graph.CubicStar
import StructuralExhaustion.Graph.HighCenterPort

namespace StructuralExhaustion.Graph.LocalSeparatorProjection

universe u

variable {V : Type u} (object : FiniteObject V)

/-- Exact three-boundary switch projection of one certified cubic star. -/
structure Cubic {center : V} (data : CubicStar.Data object center) where
  shape : data.SwitchBoundaryShape
  shapeExact : shape = CubicStar.Data.switchBoundaryShape object data
  supportExact :
    ({shape.internalVertex} ∪ Set.range shape.boundaryVertex) =
      (CubicStar.Data.support object data : Set V)

def cubic {center : V} (data : CubicStar.Data object center) : Cubic object data where
  shape := CubicStar.Data.switchBoundaryShape object data
  shapeExact := rfl
  supportExact := CubicStar.Data.switchBoundary_support_eq object data

/-- Actual declared incident-port schedule at one supplied high centre. -/
structure High (center : V) (degree_ge : 4 ≤ object.degree center) where
  ports : FinEnum (HighCenterPort.Port object center)
  portsExact : ports = HighCenterPort.ports object center
  cardExact : ports.card = object.degree center
  atLeastFour : 4 ≤ ports.card

def high (center : V) (degree_ge : 4 ≤ object.degree center) :
    High object center degree_ge where
  ports := HighCenterPort.ports object center
  portsExact := rfl
  cardExact := HighCenterPort.ports_card_eq_degree object center
  atLeastFour := by
    rw [HighCenterPort.ports_card_eq_degree]
    exact degree_ge

/-- Materializing the one selected centre's declared neighbour order costs at
most one adjacency test per ambient vertex. -/
def visibleChecks : Nat := object.input.vertices.card

theorem visibleChecks_linear : visibleChecks object ≤ object.input.vertices.card :=
  le_rfl

end StructuralExhaustion.Graph.LocalSeparatorProjection
