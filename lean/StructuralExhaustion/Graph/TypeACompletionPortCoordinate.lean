import StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Graph.TypeACompletionPortCoordinate

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)

/-!
# Type A completion-port coordinates

This is the next literal D2 datum after the canonical D5 receiver traces.  A
completion port is an actual oriented ambient edge whose source is an internal
low-degree receiver and whose target lies outside the supplied Type A support.

The executable schedule first scans the already computed receiver set and then
only the actual ordered neighbours of each receiver.  Ambient cubicity makes
each nested scan have length three.  No ambient pair, path, support, context,
state, or graph universe is enumerated.
-/

/-- Internal low-degree receivers in the supplied support. -/
abbrev Receiver :=
  {vertex : profile.Vertex //
    (profile.supportObject object).degree vertex ≤ 2}

noncomputable def receiverDecidable (vertex : profile.Vertex) :
    Decidable ((profile.supportObject object).degree vertex ≤ 2) :=
  inferInstance

/-- Exact receiver scan inherited from the supplied support order. -/
@[implicit_reducible]
noncomputable def receivers : FinEnum (Receiver object profile) :=
  Core.Enumeration.subtype
    (profile.supportObject object).input.vertices
    (fun vertex => (profile.supportObject object).degree vertex ≤ 2)
    (receiverDecidable object profile)

/-- An actual neighbor of one fixed receiver. -/
abbrev Neighbor (receiver : Receiver object profile) :=
  {outside : V // object.graph.Adj receiver.1.1 outside}

/-- Exact enumeration of the actual ordered neighbor list at one receiver. -/
@[implicit_reducible]
noncomputable def neighbors (receiver : Receiver object profile) :
    FinEnum (Neighbor object profile receiver) := by
  letI : DecidableEq V := object.input.vertices.decEq
  let source := (object.input.orderedNeighbors receiver.1.1).values
  let values : List (Neighbor object profile receiver) :=
    source.attach.map fun entry =>
      ⟨entry.1, (object.input.mem_orderedNeighbors_iff _ _).1 entry.2⟩
  have sourceNodup : source.Nodup :=
    (object.input.orderedNeighbors receiver.1.1).nodup
  apply FinEnum.ofNodupList values
  · rintro ⟨neighbor, adjacent⟩
    simp [values, source]
    exact adjacent
  · exact sourceNodup.attach.map (by
      intro left right equal
      apply Subtype.ext
      exact congrArg (fun output : Neighbor object profile receiver => output.1)
        equal)

/-- Outside endpoints among the three actual incidences of one receiver. -/
abbrev Endpoint (receiver : Receiver object profile) :=
  {neighbor : Neighbor object profile receiver //
    neighbor.1 ∉ profile.support}

noncomputable def endpointDecidable (receiver : Receiver object profile)
    (neighbor : Neighbor object profile receiver) :
    Decidable (neighbor.1 ∉ profile.support) := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact inferInstance

@[implicit_reducible]
noncomputable def endpoints (receiver : Receiver object profile) :
    FinEnum (Endpoint object profile receiver) :=
  Core.Enumeration.subtype (neighbors object profile receiver)
    (fun neighbor => neighbor.1 ∉ profile.support)
    (endpointDecidable object profile receiver)

/-- One exact completion port, indexed first by its receiver and then by one
of that receiver's actual outside incidences. -/
abbrev Coordinate :=
  Sigma fun receiver : Receiver object profile =>
    Endpoint object profile receiver

/-- Dependent receiver-local completion-port schedule. -/
@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate object profile) := by
  letI : FinEnum (Receiver object profile) := receivers object profile
  letI : (receiver : Receiver object profile) →
      FinEnum (Endpoint object profile receiver) :=
    endpoints object profile
  exact inferInstance

namespace Coordinate

def receiver (coordinate : Coordinate object profile) : profile.Vertex :=
  coordinate.1.1

def outside (coordinate : Coordinate object profile) : V :=
  coordinate.2.1.1

theorem receiver_internal_degree_le_two
    (coordinate : Coordinate object profile) :
    (profile.supportObject object).degree
      (coordinate.receiver object profile) ≤ 2 :=
  coordinate.1.2

theorem receiver_ambient_degree_eq_three
    (coordinate : Coordinate object profile) :
    object.degree (coordinate.receiver object profile).1 = 3 :=
  profile.ambient_cubic _ (coordinate.receiver object profile).2

theorem adjacent (coordinate : Coordinate object profile) :
    object.graph.Adj (coordinate.receiver object profile).1
      (coordinate.outside object profile) :=
  coordinate.2.1.2

theorem outside_not_mem_support (coordinate : Coordinate object profile) :
    coordinate.outside object profile ∉ profile.support :=
  coordinate.2.2

theorem receiver_ne_outside (coordinate : Coordinate object profile) :
    (coordinate.receiver object profile).1 ≠
      coordinate.outside object profile := by
  intro equal
  apply coordinate.outside_not_mem_support object profile
  rw [← equal]
  exact (coordinate.receiver object profile).2

/-- Port labels are exact ordered incidences. -/
theorem ext {left right : Coordinate object profile}
    (receiver : left.receiver object profile =
      right.receiver object profile)
    (outside : left.outside object profile =
      right.outside object profile) :
    left = right := by
  obtain ⟨leftReceiver, leftEndpoint⟩ := left
  obtain ⟨rightReceiver, rightEndpoint⟩ := right
  change leftReceiver.1 = rightReceiver.1 at receiver
  have receiverExact : leftReceiver = rightReceiver := Subtype.ext receiver
  subst rightReceiver
  have endpointExact : leftEndpoint = rightEndpoint := by
    apply Subtype.ext
    apply Subtype.ext
    exact outside
  subst rightEndpoint
  rfl

end Coordinate

theorem neighbors_card_eq_three (receiver : Receiver object profile) :
    (neighbors object profile receiver).card = 3 := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : FinEnum (Neighbor object profile receiver) :=
    neighbors object profile receiver
  rw [FinEnum.card_eq_fintypeCard, ← Nat.card_eq_fintype_card]
  change (object.graph.neighborSet receiver.1.1).ncard = 3
  rw [← object.degree_eq_ncard_neighborSet]
  exact profile.ambient_cubic receiver.1.1 receiver.1.2

theorem endpoints_card_le_three (receiver : Receiver object profile) :
    (endpoints object profile receiver).card ≤ 3 := by
  letI : FinEnum (Neighbor object profile receiver) :=
    neighbors object profile receiver
  letI : FinEnum (Endpoint object profile receiver) :=
    endpoints object profile receiver
  have subtypeBound : Fintype.card (Endpoint object profile receiver) ≤
      Fintype.card (Neighbor object profile receiver) :=
    Fintype.card_subtype_le _
  rw [← FinEnum.card_eq_fintypeCard, ← FinEnum.card_eq_fintypeCard] at subtypeBound
  simpa [neighbors_card_eq_three object profile receiver] using subtypeBound

theorem receivers_card_le_support :
    (receivers object profile).card ≤ profile.support.card := by
  letI : FinEnum profile.Vertex :=
    (profile.supportObject object).input.vertices
  letI : FinEnum (Receiver object profile) := receivers object profile
  calc
    (receivers object profile).card ≤
        (profile.supportObject object).input.vertices.card := by
      rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
      exact Fintype.card_subtype_le _
    _ = profile.support.card :=
      object.induceFinset_vertexCount profile.support

theorem coordinates_card_le_three_mul_support :
    (coordinates object profile).card ≤ 3 * profile.support.card := by
  letI : FinEnum (Receiver object profile) := receivers object profile
  letI : (receiver : Receiver object profile) →
      FinEnum (Endpoint object profile receiver) :=
    endpoints object profile
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_sigma]
  calc
    (∑ receiver : Receiver object profile,
        Fintype.card (Endpoint object profile receiver)) ≤
        ∑ _receiver : Receiver object profile, 3 := by
      apply Finset.sum_le_sum
      intro receiver _member
      simpa [FinEnum.card_eq_fintypeCard] using
        endpoints_card_le_three object profile receiver
    _ = 3 * Fintype.card (Receiver object profile) := by
      simp [Nat.mul_comm]
    _ ≤ 3 * profile.support.card := by
      have receiverBound : Fintype.card (Receiver object profile) ≤
          profile.support.card := by
        simpa [FinEnum.card_eq_fintypeCard] using
          receivers_card_le_support object profile
      exact Nat.mul_le_mul_left 3 receiverBound

/-! Constructing the dependent schedule performs two literal local scans:
one receiver test for every support vertex, followed by one outside-support
test for every actual neighbour of every retained receiver.  Counting only
the successful endpoints would undercount these primitive decisions. -/
noncomputable def visibleChecks : Nat :=
  profile.support.card +
    ∑ receiver : Receiver object profile, (neighbors object profile receiver).card

theorem visibleChecks_eq_support_add_three_mul_receivers :
    visibleChecks object profile =
      profile.support.card + 3 * (receivers object profile).card := by
  letI : FinEnum (Receiver object profile) := receivers object profile
  unfold visibleChecks
  rw [FinEnum.card_eq_fintypeCard]
  congr 1
  calc
    (∑ receiver : Receiver object profile,
        (neighbors object profile receiver).card) =
        ∑ _receiver : Receiver object profile, 3 := by
      apply Finset.sum_congr rfl
      intro receiver _member
      exact neighbors_card_eq_three object profile receiver
    _ = 3 * Fintype.card (Receiver object profile) := by
      simp [Nat.mul_comm]

theorem visibleChecks_polynomial :
    visibleChecks object profile ≤ 4 * object.input.vertices.card := by
  have supportLe : profile.support.card ≤ object.input.vertices.card := by
    rw [← object.card_vertexFinset]
    exact Finset.card_le_card fun vertex _member => object.mem_vertexFinset vertex
  have receiverLe := receivers_card_le_support object profile
  rw [visibleChecks_eq_support_add_three_mul_receivers object profile]
  omega

/-- Linear primitive-check budget: one receiver test per support vertex plus
three actual-incidence tests per retained receiver. -/
noncomputable def budget : Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => visibleChecks object profile
  coefficient := 4
  degree := 1
  bounded := by
    intro _unit
    have bound := visibleChecks_polynomial object profile
    simpa using bound.trans (Nat.mul_le_mul_left 4 (Nat.le_succ _))

end StructuralExhaustion.Graph.TypeACompletionPortCoordinate
