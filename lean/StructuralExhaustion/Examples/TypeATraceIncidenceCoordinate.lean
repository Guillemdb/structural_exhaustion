import StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate

namespace StructuralExhaustion.Examples.TypeATraceIncidenceCoordinate

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V)
variable
  (profile : Graph.TypeACanonicalReceiverTrace.SupportProfile object)

open Graph.TypeATraceIncidenceCoordinate

/-! A non-Erdos consumer checks that the reusable D5 trace schedule exposes
only literal vertices of the supplied support and that each locally evaluated
degree assertion is inherited from the graph-owned canonical trace. -/

example (coordinate : Coordinate object profile) :
    coordinate.ambientVertex object profile ∈ profile.support :=
  coordinate.ambientVertex_mem_profile object profile

example (coordinate : Coordinate object profile) :
    object.degree (coordinate.ambientVertex object profile) = 3 :=
  coordinate.ambientVertex_degree_eq_three object profile

example (coordinate : Coordinate object profile)
    (notTerminal : ¬coordinate.IsTerminal object profile) :
    coordinate.internalDegree object profile = 3 :=
  coordinate.internalDegree_eq_three_of_not_terminal object profile notTerminal

example (coordinate : Coordinate object profile)
    (terminal : coordinate.IsTerminal object profile) :
    coordinate.internalDegree object profile ≤ 2 :=
  coordinate.internalDegree_le_two_of_terminal object profile terminal

example (cubic : profile.Cubic object) :
    cubic.1.1 ∈ profile.support ∧
      (profile.receiverSelection object cubic).vertex.1 ∈ profile.support :=
  ⟨profile.cubic_mem_support object cubic,
    profile.receiver_mem_support object cubic⟩

example (cubic : profile.Cubic object) :
    cubic.1 ≠ (profile.receiverSelection object cubic).vertex ∧
      0 < (profile.trace object cubic).length :=
  ⟨profile.cubic_ne_receiver object cubic,
    profile.trace_length_pos object cubic⟩

example (cubic : profile.Cubic object) :
    (profile.trace object cubic).support.Nodup :=
  profile.trace_support_nodup object cubic

example (cubic : profile.Cubic object) :
    cubic.1 ∈ (profile.trace object cubic).support ∧
      (profile.receiverSelection object cubic).vertex ∈
        (profile.trace object cubic).support :=
  ⟨profile.cubic_mem_trace_support object cubic,
    profile.receiver_mem_trace_support object cubic⟩

example (cubic : profile.Cubic object) {index : Nat}
    (bound : index < (profile.trace object cubic).length) :
    object.graph.Adj
      ((profile.trace object cubic).getVert index).1
      ((profile.trace object cubic).getVert (index + 1)).1 :=
  profile.trace_successive_ambient_adjacent object cubic bound

example :
    (coordinates object profile).card ≤ visibleChecks object profile :=
  coordinates_card_le_visibleChecks object profile

example :
    visibleChecks object profile ≤
      object.input.vertices.card * (object.input.vertices.card + 1) :=
  visibleChecks_polynomial object profile

example :
    (budget object profile).checks () ≤
      (budget object profile).coefficient *
        ((budget object profile).size () + 1) ^
          (budget object profile).degree :=
  (budget object profile).bounded ()

end StructuralExhaustion.Examples.TypeATraceIncidenceCoordinate
