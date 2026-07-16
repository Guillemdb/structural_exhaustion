import StructuralExhaustion.Core.WorkBudget
import StructuralExhaustion.Graph.TypeBFanCenterCoordinate

namespace StructuralExhaustion.Graph.TypeBFanShoulderIncidenceCoordinate

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-!
# D6 non-center fan-incidence coordinates

After a Type B center is known, deletion criticality makes every incident port
endpoint cubic.  Consequently its two non-center incidences are exactly the
two entries of `HighCenterPort.shoulderVertices`.  This module schedules those
literal incidences as `port × Fin 2`.

This is only an incidence subfamily of D6.  It does not classify an incidence
as window/non-window, assert that a port is fan-closed, attach a certificate
label, or compare two ports.
-/

structure Profile where
  center : V
  centerHigh : 4 ≤ object.degree center
  deletionCritical : ∀ dart : object.graph.Dart,
    object.degree dart.fst = 3 ∨ object.degree dart.snd = 3

def Profile.centerProfile (profile : Profile object) :
    TypeBFanCenterCoordinate.Profile object where
  center := profile.center
  centerHigh := profile.centerHigh

abbrev Coordinate (profile : Profile object) :=
  HighCenterPort.Port object profile.center × Fin 2

/-- Exactly two non-center incidence slots for every literal center port. -/
@[implicit_reducible]
def coordinates (profile : Profile object) :
    FinEnum (Coordinate object profile) := by
  letI : FinEnum (HighCenterPort.Port object profile.center) :=
    HighCenterPort.ports object profile.center
  infer_instance

namespace Coordinate

variable (profile : Profile object)

def port (coordinate : Coordinate object profile) :
    HighCenterPort.Port object profile.center :=
  coordinate.1

def endpoint (coordinate : Coordinate object profile) : V :=
  HighCenterPort.endpoint object profile.center coordinate.port

/-- The literal non-center neighbour selected by the `Fin 2` side. -/
def shoulder (coordinate : Coordinate object profile) : V :=
  (HighCenterPort.shoulderVertices object profile.center coordinate.port).get
    ⟨coordinate.2.1, by
      rw [HighCenterPort.shoulderVertices_length object profile.center
        profile.centerHigh profile.deletionCritical coordinate.port]
      exact coordinate.2.2⟩

noncomputable def support (coordinate : Coordinate object profile) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {profile.center, coordinate.endpoint object profile,
    coordinate.shoulder object profile}

/-- Literal value read at one D6 shoulder-incidence coordinate. -/
structure Value (coordinate : Coordinate object profile) where
  center : V
  centerExact : center = profile.center
  portEndpoint : V
  portEndpointExact : portEndpoint = coordinate.endpoint object profile
  shoulder : V
  shoulderExact : shoulder = coordinate.shoulder object profile

def value (coordinate : Coordinate object profile) :
    coordinate.Value object profile where
  center := profile.center
  centerExact := rfl
  portEndpoint := coordinate.endpoint object profile
  portEndpointExact := rfl
  shoulder := coordinate.shoulder object profile
  shoulderExact := rfl

theorem center_incident (coordinate : Coordinate object profile) :
    object.graph.Adj profile.center (coordinate.endpoint object profile) :=
  HighCenterPort.endpoint_adjacent object profile.center coordinate.port

theorem endpoint_cubic (coordinate : Coordinate object profile) :
    object.degree (coordinate.endpoint object profile) = 3 :=
  HighCenterPort.endpoint_cubic object profile.center profile.centerHigh
    profile.deletionCritical coordinate.port

theorem shoulder_mem (coordinate : Coordinate object profile) :
    coordinate.shoulder object profile ∈
      HighCenterPort.shoulderVertices object profile.center coordinate.port := by
  unfold shoulder
  exact List.get_mem _ _

theorem shoulder_incident (coordinate : Coordinate object profile) :
    object.graph.Adj (coordinate.endpoint object profile)
      (coordinate.shoulder object profile) :=
  HighCenterPort.adjacent_of_mem_shoulders object profile.center coordinate.port
    (coordinate.shoulder_mem object profile)

theorem shoulder_ne_center (coordinate : Coordinate object profile) :
    coordinate.shoulder object profile ≠ profile.center :=
  HighCenterPort.ne_center_of_mem_shoulders object profile.center coordinate.port
    (coordinate.shoulder_mem object profile)

theorem center_mem_support (coordinate : Coordinate object profile) :
    profile.center ∈ coordinate.support object profile := by
  simp [support]

theorem endpoint_mem_support (coordinate : Coordinate object profile) :
    coordinate.endpoint object profile ∈ coordinate.support object profile := by
  simp [support]

theorem shoulder_mem_support (coordinate : Coordinate object profile) :
    coordinate.shoulder object profile ∈ coordinate.support object profile := by
  simp [support]

end Coordinate

theorem coordinates_card_eq_two_mul_degree (profile : Profile object) :
    (coordinates object profile).card = 2 * object.degree profile.center := by
  letI : FinEnum (HighCenterPort.Port object profile.center) :=
    HighCenterPort.ports object profile.center
  have lengthEq :
      (object.input.orderedNeighbors profile.center).values.length =
        object.degree profile.center := by
    simpa [FiniteObject.degree] using
      object.input.orderedNeighbors_length profile.center
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_prod, Fintype.card_fin,
    lengthEq]
  norm_num
  omega

def visibleChecks (profile : Profile object) : Nat :=
  (coordinates object profile).card

/-- The first literal shoulder-incidence coordinate.  Its existence uses only
the already proved high degree of the center; no port family is searched. -/
def firstCoordinate (profile : Profile object) : Coordinate object profile :=
  (⟨0, by
      have degreePositive : 0 < object.degree profile.center := by
        exact lt_of_lt_of_le (by decide) profile.centerHigh
      have lengthEq :
          (object.input.orderedNeighbors profile.center).values.length =
            object.degree profile.center := by
        simpa [FiniteObject.degree] using
          object.input.orderedNeighbors_length profile.center
      rw [lengthEq]
      exact degreePositive⟩,
    ⟨0, by decide⟩)

theorem firstCoordinate_port_index (profile : Profile object) :
    (firstCoordinate object profile).1.1 = 0 :=
  rfl

theorem firstCoordinate_side_index (profile : Profile object) :
    (firstCoordinate object profile).2.1 = 0 :=
  rfl

theorem visibleChecks_linear (profile : Profile object) :
    visibleChecks object profile ≤ 2 * object.input.vertices.card := by
  rw [visibleChecks, coordinates_card_eq_two_mul_degree]
  exact Nat.mul_le_mul_left 2
    (HighCenterPort.degree_le_vertexCount object profile.center)

/-- Two primitive incidence reads per declared center port. -/
def budget (profile : Profile object) : Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => visibleChecks object profile
  coefficient := 2
  degree := 1
  bounded := by
    intro _unit
    have bound := visibleChecks_linear object profile
    calc
      visibleChecks object profile ≤ 2 * object.input.vertices.card := bound
      _ ≤ 2 * (object.input.vertices.card + 1) ^ 1 := by
        simp

end StructuralExhaustion.Graph.TypeBFanShoulderIncidenceCoordinate
