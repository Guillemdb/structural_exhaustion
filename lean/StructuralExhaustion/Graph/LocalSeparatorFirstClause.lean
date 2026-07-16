import StructuralExhaustion.Graph.LocalSeparatorSemanticFrontier

namespace StructuralExhaustion.Graph.LocalSeparatorFirstClause

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-!
# First literal clauses from a local separator

These certificates expose only incidence data already forced by the exact
separator payload.  They carry no response, CT3, Type-B, capacity, sparse-exit,
or target semantics.
-/

structure Cubic {center : V} {data : CubicStar.Data object center}
    (projection : LocalSeparatorProjection.Cubic object data) where
  boundary : Fin 3 → V
  boundaryExact : boundary = projection.shape.boundaryVertex
  boundaryInjective : Function.Injective boundary
  boundaryAdjacent : ∀ index,
    object.graph.Adj projection.shape.internalVertex (boundary index)

def cubic {center : V} {data : CubicStar.Data object center}
    (projection : LocalSeparatorProjection.Cubic object data) :
    Cubic object projection where
  boundary := projection.shape.boundaryVertex
  boundaryExact := rfl
  boundaryInjective := projection.shape.boundaryInjective
  boundaryAdjacent := projection.shape.boundaryAdjacent

/-- The first four positions in the already declared neighbour schedule. -/
def firstFourPorts (center : V) (degree_ge : 4 ≤ object.degree center) :
    Fin 4 → HighCenterPort.Port object center :=
  fun index => ⟨index.val, by
    have lengthEq : (object.input.orderedNeighbors center).values.length =
        object.degree center := object.input.orderedNeighbors_length center
    rw [lengthEq]
    exact index.isLt.trans_le degree_ge⟩

theorem firstFourPorts_injective (center : V)
    (degree_ge : 4 ≤ object.degree center) :
    Function.Injective (firstFourPorts object center degree_ge) := by
  intro left right equal
  apply Fin.ext
  exact congrArg
    (fun port : HighCenterPort.Port object center => port.val) equal

structure High (center : V) (degree_ge : 4 ≤ object.degree center)
    (projection : LocalSeparatorProjection.High object center degree_ge) where
  port : Fin 4 → HighCenterPort.Port object center
  portExact : port = firstFourPorts object center degree_ge
  portInjective : Function.Injective port
  endpointAdjacent : ∀ index,
    object.graph.Adj center (HighCenterPort.endpoint object center (port index))
  endpointInjective : Function.Injective
    (fun index => HighCenterPort.endpoint object center (port index))

def high (center : V) (degree_ge : 4 ≤ object.degree center)
    (projection : LocalSeparatorProjection.High object center degree_ge) :
    High object center degree_ge projection where
  port := firstFourPorts object center degree_ge
  portExact := rfl
  portInjective := firstFourPorts_injective object center degree_ge
  endpointAdjacent := fun index =>
    HighCenterPort.endpoint_adjacent object center _
  endpointInjective := by
    intro left right equal
    exact firstFourPorts_injective object center degree_ge
      (HighCenterPort.endpoint_injective object center equal)

/-- The certificates use fixed arity and inspect no ambient universe. -/
def visibleChecks : Nat := 4

theorem visibleChecks_constant : visibleChecks ≤ 4 := le_rfl

end StructuralExhaustion.Graph.LocalSeparatorFirstClause
