import StructuralExhaustion.Graph.FanClosedPort
import StructuralExhaustion.Graph.TypeBFanShoulderIncidenceCoordinate

namespace StructuralExhaustion.Graph.InducedCoreFanAssignment

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-!
# Induced-core assignment on one actual fan port

The assignment judgment is derived from a finite vertex core: a carrier is
assigned exactly when it is a literal graph edge whose two ends lie in the
core. The whole-port classifier reads only the two declared shoulders of one
actual port and returns both assignment proofs or the first failed carrier.
-/

def Assigned (core : Finset V) (carrier : FanClosedPort.LocalCarrier V) : Prop :=
  object.graph.Adj carrier.1 carrier.2 ∧
    carrier.1 ∈ core ∧ carrier.2 ∈ core

noncomputable def assignedDecidable (core : Finset V) :
    ∀ carrier, Decidable (Assigned object core carrier) := by
  intro carrier
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold Assigned
  exact inferInstance

theorem assigned_of_mem (core : Finset V)
    (carrier : FanClosedPort.LocalCarrier V)
    (adjacent : object.graph.Adj carrier.1 carrier.2)
    (first : carrier.1 ∈ core) (second : carrier.2 ∈ core) :
    Assigned object core carrier :=
  ⟨adjacent, first, second⟩

theorem not_assigned_of_first_not_mem (core : Finset V)
    (carrier : FanClosedPort.LocalCarrier V) (outside : carrier.1 ∉ core) :
    ¬Assigned object core carrier := by
  intro assigned
  exact outside assigned.2.1

theorem not_assigned_of_second_not_mem (core : Finset V)
    (carrier : FanClosedPort.LocalCarrier V) (outside : carrier.2 ∉ core) :
    ¬Assigned object core carrier := by
  intro assigned
  exact outside assigned.2.2

variable (profile : TypeBFanShoulderIncidenceCoordinate.Profile object)

abbrev Port := HighCenterPort.Port object profile.center

def coordinate (port : Port object profile) (side : Fin 2) :
    TypeBFanShoulderIncidenceCoordinate.Coordinate object profile :=
  (port, side)

def carrier (port : Port object profile) (side : Fin 2) :
    FanClosedPort.LocalCarrier V :=
  (TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint object profile
      (coordinate object profile port side),
    TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder object profile
      (coordinate object profile port side))

theorem carrier_adjacent (port : Port object profile) (side : Fin 2) :
    object.graph.Adj (carrier object profile port side).1
      (carrier object profile port side).2 :=
  TypeBFanShoulderIncidenceCoordinate.Coordinate.shoulder_incident object profile
    (coordinate object profile port side)

def firstSide : Fin 2 := ⟨0, by decide⟩
def secondSide : Fin 2 := ⟨1, by decide⟩

theorem firstCarrier_eq_fanClosedCarrier
    (port : FanClosedPort.OpenPort profile.centerHigh profile.deletionCritical) :
    carrier object profile port.1 firstSide =
      FanClosedPort.carrier profile.centerHigh profile.deletionCritical port false := by
  rfl

theorem secondCarrier_eq_fanClosedCarrier
    (port : FanClosedPort.OpenPort profile.centerHigh profile.deletionCritical) :
    carrier object profile port.1 secondSide =
      FanClosedPort.carrier profile.centerHigh profile.deletionCritical port true := by
  rfl

/-- Exhaustive fixed-order result for one actual port. -/
inductive Availability (core : Finset V) (port : Port object profile) where
  | both
      (first : Assigned object core (carrier object profile port firstSide))
      (second : Assigned object core (carrier object profile port secondSide))
  | firstMissing
      (missing : ¬Assigned object core
        (carrier object profile port firstSide))
  | secondMissing
      (first : Assigned object core (carrier object profile port firstSide))
      (missing : ¬Assigned object core
        (carrier object profile port secondSide))

/-- Inspect exactly side `0`, then side `1`; hence the returned failure is the
first missing assignment in the declared shoulder order. -/
noncomputable def classify (core : Finset V) (port : Port object profile) :
    Availability object profile core port := by
  by_cases first : Assigned object core
      (carrier object profile port firstSide)
  · by_cases second : Assigned object core
        (carrier object profile port secondSide)
    · exact .both first second
    · exact .secondMissing first second
  · exact .firstMissing first

def visibleChecks : Nat := 2

theorem visibleChecks_constant : visibleChecks = 2 := rfl

end StructuralExhaustion.Graph.InducedCoreFanAssignment
