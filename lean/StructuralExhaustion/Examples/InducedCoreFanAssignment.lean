import StructuralExhaustion.Graph.InducedCoreFanAssignment

namespace StructuralExhaustion.Examples.InducedCoreFanAssignment

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : Graph.TypeBFanShoulderIncidenceCoordinate.Profile object)
variable (core : Finset V)

open Graph.InducedCoreFanAssignment

/-- Non-Erdős transfer: membership of the endpoint and both literal
shoulders constructs the proof-carrying whole-port result. -/
theorem both_of_all_mem (port : Port object profile)
    (endpoint :
      (carrier object profile port firstSide).1 ∈ core)
    (firstShoulder :
      (carrier object profile port firstSide).2 ∈ core)
    (secondShoulder :
      (carrier object profile port secondSide).2 ∈ core) :
    Nonempty (Availability object profile core port) := by
  exact ⟨.both
    (assigned_of_mem object core _ (carrier_adjacent object profile port firstSide)
      endpoint firstShoulder)
    (assigned_of_mem object core _ (carrier_adjacent object profile port secondSide)
      (by simpa [carrier, coordinate,
          Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.endpoint,
          Graph.TypeBFanShoulderIncidenceCoordinate.Coordinate.port] using endpoint)
      secondShoulder)⟩

/-- Non-Erdős transfer: an endpoint outside the core forces the declared first
carrier to be the first missing assignment. -/
theorem first_missing_of_endpoint_outside (port : Port object profile)
    (outside : (carrier object profile port firstSide).1 ∉ core) :
    ∃ missing : ¬Assigned object core (carrier object profile port firstSide),
      Availability.firstMissing missing = classify object profile core port := by
  have missing := not_assigned_of_first_not_mem object core _ outside
  unfold classify
  split
  · contradiction
  · exact ⟨missing, rfl⟩

end StructuralExhaustion.Examples.InducedCoreFanAssignment
