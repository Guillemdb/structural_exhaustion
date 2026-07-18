import StructuralExhaustion.Graph.TypeACanonicalReceiverTrace
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)

/-!
# D5 canonical-trace incidence coordinates

This is the first finite subfamily of manuscript clause D5.  A coordinate is
one actual position on the canonical Type A receiver trace of one internal
cubic source.  Its declared support is the complete parent trace (the label is
the trace together with its position), and its value records the literal
ambient vertex, internal degree, and terminal role.

The schedule is the dependent sum of the declared cubic-source order and each
stored trace order.  It does not enumerate paths, supports, contexts, or graph
families and does not claim the later completion-port/channel/basin clauses.
-/

abbrev TracePosition (cubic : profile.Cubic object) :=
  Fin ((SupportProfile.trace object profile cubic).length + 1)

abbrev Coordinate :=
  Sigma fun cubic : profile.Cubic object => TracePosition object profile cubic

/-- Exact finite dependent coordinate schedule. -/
@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate object profile) := by
  letI : FinEnum (profile.Cubic object) := SupportProfile.cubics object profile
  letI : (cubic : profile.Cubic object) →
      FinEnum (TracePosition object profile cubic) := fun _ => inferInstance
  exact inferInstance

namespace Coordinate

noncomputable def source (coordinate : Coordinate object profile) :
    profile.Cubic object := coordinate.1

noncomputable def position (coordinate : Coordinate object profile) : Nat :=
  coordinate.2.1

theorem position_le_length (coordinate : Coordinate object profile) :
    coordinate.position object profile ≤
      (SupportProfile.trace object profile
        (coordinate.source object profile)).length := by
  exact Nat.le_of_lt_succ coordinate.2.2

noncomputable def vertex (coordinate : Coordinate object profile) :
    profile.Vertex :=
  (SupportProfile.trace object profile
    (coordinate.source object profile)).getVert
    (coordinate.position object profile)

noncomputable def ambientVertex (coordinate : Coordinate object profile) : V :=
  (coordinate.vertex object profile).1

noncomputable def support (coordinate : Coordinate object profile) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact ((SupportProfile.trace object profile
    (coordinate.source object profile)).support.map
      (fun vertex => vertex.1)).toFinset

theorem ambientVertex_mem_support (coordinate : Coordinate object profile) :
    coordinate.ambientVertex object profile ∈ coordinate.support object profile := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [support, List.mem_toFinset, List.mem_map]
  refine ⟨coordinate.vertex object profile, ?_, rfl⟩
  exact (SupportProfile.trace object profile
    (coordinate.source object profile)).getVert_mem_support
      (coordinate.position object profile)

theorem support_subset_profile (coordinate : Coordinate object profile) :
    coordinate.support object profile ⊆ profile.support := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex member
  rw [support, List.mem_toFinset, List.mem_map] at member
  rcases member with ⟨supportVertex, _supportMember, rfl⟩
  exact supportVertex.2

theorem source_mem_support (coordinate : Coordinate object profile) :
    (coordinate.source object profile).1.1 ∈ coordinate.support object profile := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [support, List.mem_toFinset, List.mem_map]
  refine ⟨(coordinate.source object profile).1, ?_, rfl⟩
  exact (SupportProfile.trace object profile
    (coordinate.source object profile)).start_mem_support

theorem support_card_eq_length_add_one
    (coordinate : Coordinate object profile) :
    (coordinate.support object profile).card =
      (SupportProfile.trace object profile
        (coordinate.source object profile)).length + 1 := by
  letI : DecidableEq V := object.input.vertices.decEq
  let trace := SupportProfile.trace object profile
    (coordinate.source object profile)
  have traceNodup : trace.support.Nodup :=
    (profile.trace_isPath object (coordinate.source object profile)).support_nodup
  have ambientNodup : (trace.support.map (fun vertex => vertex.1)).Nodup := by
    exact traceNodup.map fun left right equal => Subtype.ext equal
  rw [support, List.toFinset_card_of_nodup ambientNodup, List.length_map]
  exact trace.length_support

noncomputable def internalDegree (coordinate : Coordinate object profile) : Nat :=
  (profile.supportObject object).degree (coordinate.vertex object profile)

def IsTerminal (coordinate : Coordinate object profile) : Prop :=
  coordinate.position object profile =
    (SupportProfile.trace object profile
      (coordinate.source object profile)).length

noncomputable def terminalDecidable (coordinate : Coordinate object profile) :
    Decidable (coordinate.IsTerminal object profile) :=
  Classical.propDecidable _

noncomputable def terminal (coordinate : Coordinate object profile) : Bool :=
  @decide (coordinate.IsTerminal object profile)
    (coordinate.terminalDecidable object profile)

/-- Literal locally evaluated D5 trace-incidence value. -/
structure Value (coordinate : Coordinate object profile) where
  ambientVertex : V
  ambientVertexExact : ambientVertex = coordinate.ambientVertex object profile
  internalDegree : Nat
  internalDegreeExact : internalDegree = coordinate.internalDegree object profile
  terminal : Bool
  terminalExact : terminal = coordinate.terminal object profile

noncomputable def value (coordinate : Coordinate object profile) :
    coordinate.Value object profile where
  ambientVertex := coordinate.ambientVertex object profile
  ambientVertexExact := rfl
  internalDegree := coordinate.internalDegree object profile
  internalDegreeExact := rfl
  terminal := coordinate.terminal object profile
  terminalExact := rfl

theorem ambientVertex_mem_profile
    (coordinate : Coordinate object profile) :
    coordinate.ambientVertex object profile ∈ profile.support :=
  (coordinate.vertex object profile).2

theorem ambientVertex_degree_eq_three
    (coordinate : Coordinate object profile) :
    object.degree (coordinate.ambientVertex object profile) = 3 :=
  profile.ambient_cubic _ (coordinate.ambientVertex_mem_profile object profile)

theorem terminal_true_iff (coordinate : Coordinate object profile) :
    coordinate.terminal object profile = true ↔
      coordinate.IsTerminal object profile := by
  unfold terminal
  exact @decide_eq_true_iff (coordinate.IsTerminal object profile)
    (coordinate.terminalDecidable object profile)

theorem internalDegree_eq_three_of_not_terminal
    (coordinate : Coordinate object profile)
    (notTerminal : ¬coordinate.IsTerminal object profile) :
    coordinate.internalDegree object profile = 3 := by
  have before : coordinate.position object profile <
      (SupportProfile.trace object profile
        (coordinate.source object profile)).length := by
    have le := coordinate.position_le_length object profile
    unfold IsTerminal at notTerminal
    exact lt_of_le_of_ne le notTerminal
  exact profile.receiverSelection_internal_degree_eq_three object
    (coordinate.source object profile) (coordinate.position object profile)
    before

theorem internalDegree_le_two_of_terminal
    (coordinate : Coordinate object profile)
    (terminal : coordinate.IsTerminal object profile) :
    coordinate.internalDegree object profile ≤ 2 := by
  unfold internalDegree vertex
  rw [terminal]
  simpa only [SimpleGraph.Walk.getVert_length] using
    profile.receiver_degree_le_two object (coordinate.source object profile)

end Coordinate

/-- Every retained simple trace has fewer vertices-as-edges than the declared
support has vertices.  This is a local support bound, not an ambient search. -/
theorem trace_length_lt_support_card (cubic : profile.Cubic object) :
    (SupportProfile.trace object profile cubic).length < profile.support.card := by
  letI : FinEnum profile.Vertex := (profile.supportObject object).input.vertices
  have pathBound := (profile.trace_isPath object cubic).length_lt
  simpa [FinEnum.card_eq_fintypeCard] using pathBound

/-- Inject the dependent trace-position schedule into one support vertex and
one bounded local index. -/
noncomputable def coordinateEmbedding :
    Coordinate object profile → profile.Vertex × Fin (profile.support.card + 1) :=
  fun coordinate =>
    ⟨coordinate.1.1, ⟨coordinate.2.1, by
      have positionLe := coordinate.position_le_length object profile
      have traceLt := trace_length_lt_support_card object profile coordinate.1
      omega⟩⟩

theorem coordinateEmbedding_injective :
    Function.Injective (coordinateEmbedding object profile) := by
  intro left right equal
  obtain ⟨leftSource, leftPosition⟩ := left
  obtain ⟨rightSource, rightPosition⟩ := right
  have sourceEqual : leftSource = rightSource := by
    apply Subtype.ext
    have sourceVertexEqual := congrArg Prod.fst equal
    change leftSource.1 = rightSource.1 at sourceVertexEqual
    exact sourceVertexEqual
  subst rightSource
  have positionEqual : leftPosition = rightPosition := by
    apply Fin.ext
    exact congrArg (fun output => output.2.1) equal
  subst rightPosition
  rfl

/-- The dependent trace-incidence schedule has at most `|X|(|X|+1)` entries:
at most `|X|` cubic roots and at most `|X|+1` positions on each simple path. -/
noncomputable def visibleChecks : Nat :=
  profile.support.card * (profile.support.card + 1)

/-- Exact cardinality of the dependent schedule before applying its local
support bound. -/
theorem coordinates_card_eq_sum :
    (coordinates object profile).card =
      ∑ cubic : profile.Cubic object,
        ((SupportProfile.trace object profile cubic).length + 1) := by
  letI : FinEnum (profile.Cubic object) := SupportProfile.cubics object profile
  letI : (cubic : profile.Cubic object) →
      FinEnum (TracePosition object profile cubic) := fun _ => inferInstance
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_sigma]
  simp

theorem coordinates_card_le_visibleChecks :
    (coordinates object profile).card ≤ visibleChecks object profile := by
  letI : FinEnum (profile.Cubic object) := SupportProfile.cubics object profile
  letI : (cubic : profile.Cubic object) →
      FinEnum (TracePosition object profile cubic) := fun _ => inferInstance
  letI : FinEnum profile.Vertex := (profile.supportObject object).input.vertices
  rw [FinEnum.card_eq_fintypeCard]
  calc
    Fintype.card (Coordinate object profile) ≤
        Fintype.card (profile.Vertex × Fin (profile.support.card + 1)) :=
      Fintype.card_le_of_injective (coordinateEmbedding object profile)
        (coordinateEmbedding_injective object profile)
    _ = visibleChecks object profile := by
      simp [visibleChecks]

theorem visibleChecks_polynomial :
    visibleChecks object profile ≤
      object.input.vertices.card * (object.input.vertices.card + 1) := by
  have supportLe : profile.support.card ≤ object.input.vertices.card := by
    rw [← object.card_vertexFinset]
    apply Finset.card_le_card
    intro vertex _member
    exact object.mem_vertexFinset vertex
  unfold visibleChecks
  exact Nat.mul_le_mul supportLe (Nat.add_le_add_right supportLe 1)

/-- Quadratic primitive-check budget for evaluating one literal local value
at every declared trace position. -/
noncomputable def budget : Core.PolynomialCheckBudget Unit where
  size := fun _ => object.input.vertices.card
  checks := fun _ => (coordinates object profile).card
  coefficient := 1
  degree := 2
  bounded := by
    intro _unit
    have scheduleBound := coordinates_card_le_visibleChecks object profile
    have ambientBound := visibleChecks_polynomial object profile
    calc
      (coordinates object profile).card ≤ visibleChecks object profile :=
        scheduleBound
      _ ≤ object.input.vertices.card *
          (object.input.vertices.card + 1) := ambientBound
      _ ≤ 1 * (object.input.vertices.card + 1) ^ 2 := by
        nlinarith

end StructuralExhaustion.Graph.TypeATraceIncidenceCoordinate
