import StructuralExhaustion.Graph.LocalSeparatorFirstClause

namespace StructuralExhaustion.Graph.LocalSeparatorPairwiseClause

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-! Pairwise local clauses derived from fixed separator incidences. -/

structure Cubic {center : V} {data : CubicStar.Data object center}
    {projection : LocalSeparatorProjection.Cubic object data}
    (first : LocalSeparatorFirstClause.Cubic object projection) where
  boundaryPairwise : ∀ {left right : Fin 3}, left ≠ right →
    first.boundary left ≠ first.boundary right
  internal_ne_boundary : ∀ index,
    projection.shape.internalVertex ≠ first.boundary index

def cubic {center : V} {data : CubicStar.Data object center}
    {projection : LocalSeparatorProjection.Cubic object data}
    (first : LocalSeparatorFirstClause.Cubic object projection) :
    Cubic object first where
  boundaryPairwise := fun distinct equal => distinct (first.boundaryInjective equal)
  internal_ne_boundary := fun index => (first.boundaryAdjacent index).ne

structure High {center : V} {degree_ge : 4 ≤ object.degree center}
    {projection : LocalSeparatorProjection.High object center degree_ge}
    (first : LocalSeparatorFirstClause.High object center degree_ge projection) where
  endpointPairwise : ∀ {left right : Fin 4}, left ≠ right →
    HighCenterPort.endpoint object center (first.port left) ≠
      HighCenterPort.endpoint object center (first.port right)
  center_ne_endpoint : ∀ index,
    center ≠ HighCenterPort.endpoint object center (first.port index)

def high {center : V} {degree_ge : 4 ≤ object.degree center}
    {projection : LocalSeparatorProjection.High object center degree_ge}
    (first : LocalSeparatorFirstClause.High object center degree_ge projection) :
    High object first where
  endpointPairwise := fun distinct equal => distinct (first.endpointInjective equal)
  center_ne_endpoint := fun index => (first.endpointAdjacent index).ne

/-- No scan: only proof projection from at most four fixed incidences. -/
def visibleChecks : Nat := 0

theorem visibleChecks_eq_zero : visibleChecks = 0 := rfl

end StructuralExhaustion.Graph.LocalSeparatorPairwiseClause
