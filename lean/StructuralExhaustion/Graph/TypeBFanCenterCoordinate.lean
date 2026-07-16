import StructuralExhaustion.Core.WorkBudget
import StructuralExhaustion.Graph.HighCenterPort

namespace StructuralExhaustion.Graph.TypeBFanCenterCoordinate

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-!
# D6 fan-center incidence coordinates

This module implements the first dependency-free local subfamily of manuscript
clause D6.  Once a Type B branch has supplied one actual high center, the
coordinate schedule is exactly the center's declared neighbor order.  A value
records the literal center--neighbor incidence and the center degree.  It does
not assert fan safety, certificate labels, closedness, or any later bridge
ledger property.

The schedule has `degree center` entries and therefore inspects at most one
declared neighbor per ambient vertex.  It never enumerates neighbor pairs,
paths, supports, response functions, or ambient graphs.
-/

/-- Exact input available at the first Type B handoff: one literal center and
its already proved high-degree certificate. -/
structure Profile where
  center : V
  centerHigh : 4 ≤ object.degree center

abbrev Coordinate (profile : Profile object) :=
  HighCenterPort.Port object profile.center

/-- The D6 fan-center incidence schedule is the existing declared port order. -/
@[implicit_reducible]
def coordinates (profile : Profile object) :
    FinEnum (Coordinate object profile) :=
  HighCenterPort.ports object profile.center

namespace Coordinate

variable (profile : Profile object)

def endpoint (coordinate : Coordinate object profile) : V :=
  HighCenterPort.endpoint object profile.center coordinate

noncomputable def support (coordinate : Coordinate object profile) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {profile.center, coordinate.endpoint object profile}

/-- Literal locally evaluated value of one fan-center incidence. -/
structure Value (coordinate : Coordinate object profile) where
  center : V
  centerExact : center = profile.center
  endpoint : V
  endpointExact : endpoint = coordinate.endpoint object profile
  centerDegree : Nat
  centerDegreeExact : centerDegree = object.degree profile.center

def value (coordinate : Coordinate object profile) :
    coordinate.Value object profile where
  center := profile.center
  centerExact := rfl
  endpoint := coordinate.endpoint object profile
  endpointExact := rfl
  centerDegree := object.degree profile.center
  centerDegreeExact := rfl

theorem incident (coordinate : Coordinate object profile) :
    object.graph.Adj profile.center (coordinate.endpoint object profile) :=
  HighCenterPort.endpoint_adjacent object profile.center coordinate

theorem center_degree_ge_four (_coordinate : Coordinate object profile) :
    4 ≤ object.degree profile.center :=
  profile.centerHigh

theorem center_mem_support (coordinate : Coordinate object profile) :
    profile.center ∈ coordinate.support object profile := by
  simp [support]

theorem endpoint_mem_support (coordinate : Coordinate object profile) :
    coordinate.endpoint object profile ∈ coordinate.support object profile := by
  simp [support]

end Coordinate

theorem coordinates_card_eq_degree (profile : Profile object) :
    (coordinates object profile).card = object.degree profile.center :=
  HighCenterPort.ports_card_eq_degree object profile.center

/-- One primitive adjacency/value read for each literal incident port. -/
def visibleChecks (profile : Profile object) : Nat :=
  (coordinates object profile).card

theorem visibleChecks_linear (profile : Profile object) :
    visibleChecks object profile ≤ object.input.vertices.card := by
  rw [visibleChecks, coordinates_card_eq_degree]
  exact HighCenterPort.degree_le_vertexCount object profile.center

/-- Linear check budget for this exact D6 subfamily. -/
def budget (profile : Profile object) : Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => visibleChecks object profile
  coefficient := 1
  degree := 1
  bounded := by
    intro _unit
    have bound := visibleChecks_linear object profile
    simpa using bound.trans (Nat.le_add_right _ 1)

end StructuralExhaustion.Graph.TypeBFanCenterCoordinate
