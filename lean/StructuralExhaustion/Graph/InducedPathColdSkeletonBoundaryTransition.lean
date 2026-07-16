import StructuralExhaustion.Graph.InducedPathColdSkeleton
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger
open InducedPathColdSkeleton

universe u

variable {V : Type u}

/-!
# First boundary transition on one proof-carrying path

This module scans only the edge indices of one supplied simple walk.  At each
edge it performs membership tests in the finite ambient-cubic selected-window
union.  It either proves that the whole supplied support is in that union, or
retains the first crossing and turns its inside-to-outside orientation into a
literal `InducedPathColdSkeleton.BoundaryStub`.

The deleted union here contains *all* ambient-cubic selected windows.  No
claim about a manuscript-selected cold subfamily, a cyclic successor, or a
D4--D7 semantic coordinate is made.
-/

/-- One already selected simple walk whose final vertex lies in the deleted
ambient-cubic window union. -/
structure Input (object : FiniteObject V) where
  start : V
  finish : V
  path : object.graph.Walk start finish
  isPath : path.IsPath
  finalInside : finish ∈ deletedWindowVertices object

namespace Input

variable {object : FiniteObject V}

def Inside (input : Input object) (index : Nat) : Prop :=
  input.path.getVert index ∈ deletedWindowVertices object

noncomputable def insideDecidable (input : Input object) (index : Nat) :
    Decidable (input.Inside index) := by
  classical
  exact inferInstance

/-- An edge index crosses the deleted-window union in either direction. -/
abbrev EdgeIndex (input : Input object) := Fin input.path.length

@[implicit_reducible] noncomputable def edgeEnumeration (input : Input object) :
    FinEnum input.EdgeIndex := inferInstance

noncomputable def edgeOrder (input : Input object) : List input.EdgeIndex :=
  input.edgeEnumeration.orderedValues

def TransitionAt (input : Input object) (index : input.EdgeIndex) : Prop :=
  (input.Inside index.1 ∧ ¬input.Inside (index.1 + 1)) ∨
    (¬input.Inside index.1 ∧ input.Inside (index.1 + 1))

noncomputable def transitionDecidable (input : Input object)
    (index : input.EdgeIndex) :
    Decidable (input.TransitionAt index) := by
  classical
  exact inferInstance

/-- The exact ordered edge-index scan. -/
noncomputable def scan (input : Input object) :
    Core.FiniteSearch.FirstResult input.edgeOrder input.TransitionAt :=
  Core.FiniteSearch.first input.edgeEnumeration input.TransitionAt
    input.transitionDecidable

theorem final_inside_at_length (input : Input object) :
    input.Inside input.path.length := by
  simpa [Inside, input.path.getVert_length] using input.finalInside

/-- If no edge changes membership, final membership propagates backwards
through every path position. -/
theorem inside_of_no_transition (input : Input object)
    (none : ∀ index, index ∈ input.edgeOrder →
      ¬input.TransitionAt index) :
    ∀ index, index ≤ input.path.length → input.Inside index := by
  intro index indexLe
  apply Nat.decreasingInduction (motive := fun current _ ↦ input.Inside current)
      (n := input.path.length)
  · intro current currentLt nextInside
    let edge : input.EdgeIndex := ⟨current, currentLt⟩
    have notTransition : ¬input.TransitionAt edge :=
      none edge (FinEnum.mem_orderedValues input.edgeEnumeration edge)
    by_contra notInside
    exact notTransition (Or.inr ⟨notInside, nextInside⟩)
  · exact input.final_inside_at_length
  · exact indexLe

theorem support_subset_of_no_transition (input : Input object)
    (none : ∀ index, index ∈ input.edgeOrder →
      ¬input.TransitionAt index) :
    ∀ vertex ∈ input.path.support,
      vertex ∈ deletedWindowVertices object := by
  intro vertex member
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at member
  rcases member with ⟨index, rfl, indexLe⟩
  exact input.inside_of_no_transition none index indexLe

end Input

/-- A crossing oriented from its endpoint in the deleted union to its
endpoint outside the union. -/
structure OrientedCrossing {object : FiniteObject V} (input : Input object)
    (hit : Core.FiniteSearch.FirstHit input.edgeOrder
      input.TransitionAt) where
  insideIndex : Nat
  outsideIndex : Nat
  insideVertex : V
  outsideVertex : V
  insideIndex_eq : insideIndex = hit.value ∨ insideIndex = hit.value + 1
  outsideIndex_eq : outsideIndex = hit.value + 1 ∨ outsideIndex = hit.value
  inside_eq : insideVertex = input.path.getVert insideIndex
  outside_eq : outsideVertex = input.path.getVert outsideIndex
  inside_mem : insideVertex ∈ deletedWindowVertices object
  outside_not_mem : outsideVertex ∉ deletedWindowVertices object
  adjacent : object.graph.Adj insideVertex outsideVertex

namespace OrientedCrossing

variable {object : FiniteObject V} {input : Input object}
variable {hit : Core.FiniteSearch.FirstHit input.edgeOrder
  input.TransitionAt}

theorem index_lt_length : hit.value < input.path.length := by
  exact hit.value.2

/-- Orient the exact consecutive vertices named by a first transition. -/
noncomputable def ofFirstHit : OrientedCrossing input hit := by
  by_cases forwardInside : input.Inside hit.value.1
  · have forwardOutside : ¬input.Inside (hit.value.1 + 1) := by
      rcases hit.holds with forward | reverse
      · exact forward.2
      · exact (reverse.1 forwardInside).elim
    exact {
      insideIndex := hit.value.1
      outsideIndex := hit.value.1 + 1
      insideVertex := input.path.getVert hit.value.1
      outsideVertex := input.path.getVert (hit.value.1 + 1)
      insideIndex_eq := Or.inl rfl
      outsideIndex_eq := Or.inl rfl
      inside_eq := rfl
      outside_eq := rfl
      inside_mem := forwardInside
      outside_not_mem := forwardOutside
      adjacent := input.path.adj_getVert_succ index_lt_length
    }
  · have reverseInside : input.Inside (hit.value.1 + 1) := by
      rcases hit.holds with forward | reverse
      · exact (forwardInside forward.1).elim
      · exact reverse.2
    exact {
      insideIndex := hit.value.1 + 1
      outsideIndex := hit.value.1
      insideVertex := input.path.getVert (hit.value.1 + 1)
      outsideVertex := input.path.getVert hit.value.1
      insideIndex_eq := Or.inr rfl
      outsideIndex_eq := Or.inr rfl
      inside_eq := rfl
      outside_eq := rfl
      inside_mem := reverseInside
      outside_not_mem := forwardInside
      adjacent := (input.path.adj_getVert_succ index_lt_length).symm
    }

/-- Extract an ambient-cubic selected window and its exact `Fin 13` position
from the inside endpoint. -/
noncomputable def windowPosition (crossing : OrientedCrossing input hit) :
    {entry : WindowIndex object × Fin 13 //
      AmbientCubic object entry.1 ∧
      selectedWindow object entry.1 entry.2 = crossing.insideVertex} := by
  classical
  have existsEntry : ∃ window : WindowIndex object, ∃ position : Fin 13,
      AmbientCubic object window ∧
      selectedWindow object window position = crossing.insideVertex := by
    have member := crossing.inside_mem
    simp only [deletedWindowVertices, Finset.mem_biUnion] at member
    rcases member with ⟨window, _windowUniv, member⟩
    by_cases cubic : AmbientCubic object window
    · simp only [cubic, if_pos, InducedPathPacking.mem_support_iff] at member
      rcases member with ⟨position, equal⟩
      exact ⟨window, position, cubic, equal⟩
    · simp [cubic] at member
  let window := Classical.choose existsEntry
  let position := Classical.choose (Classical.choose_spec existsEntry)
  exact ⟨(window, position),
    (Classical.choose_spec (Classical.choose_spec existsEntry)).1,
    (Classical.choose_spec (Classical.choose_spec existsEntry)).2⟩

/-- The outside endpoint belongs to the exact external-neighbour set at the
extracted ambient-cubic window position. -/
theorem outside_mem_externalNeighbors (crossing : OrientedCrossing input hit) :
    crossing.outsideVertex ∈ externalNeighbors object
      crossing.windowPosition.1.1 crossing.windowPosition.1.2 := by
  classical
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [externalNeighbors, Finset.mem_sdiff]
  constructor
  · rw [ambientNeighbors, SimpleGraph.mem_neighborFinset]
    rw [crossing.windowPosition.2.2]
    exact crossing.adjacent
  · intro internal
    have sameSupport : crossing.outsideVertex ∈
        InducedPathPacking.support object 13
          (selectedWindow object crossing.windowPosition.1.1) := by
      rw [InducedPathPacking.mem_support_iff]
      unfold internalNeighbors at internal
      rw [Finset.mem_image] at internal
      rcases internal with ⟨position, _positionMember, equal⟩
      exact ⟨position, equal⟩
    apply crossing.outside_not_mem
    simp only [deletedWindowVertices, Finset.mem_biUnion]
    refine ⟨crossing.windowPosition.1.1, Finset.mem_univ _, ?_⟩
    simp [crossing.windowPosition.2.1, sameSupport]

/-- Exact literal boundary stub obtained from this oriented crossing. -/
noncomputable def boundaryStub (crossing : OrientedCrossing input hit) :
    BoundaryStub object where
  token := ⟨crossing.windowPosition.1.1,
    crossing.windowPosition.1.2,
    ⟨crossing.outsideVertex, crossing.outside_mem_externalNeighbors⟩⟩
  cubic := crossing.windowPosition.2.1
  outside := by
    classical
    letI : DecidableEq V := object.input.vertices.decEq
    rw [outsideVertices, Finset.mem_sdiff]
    exact ⟨object.mem_vertexFinset crossing.outsideVertex,
      crossing.outside_not_mem⟩

theorem boundaryStub_neighbor_eq (crossing : OrientedCrossing input hit) :
    crossing.boundaryStub.neighbor = crossing.outsideVertex := rfl

theorem boundaryStub_window_vertex_eq
    (crossing : OrientedCrossing input hit) :
    selectedWindow object crossing.boundaryStub.window
      crossing.boundaryStub.offset = crossing.insideVertex :=
  crossing.windowPosition.2.2

end OrientedCrossing

/-- Exact exhaustive result of the one-path scan. -/
inductive Result {object : FiniteObject V} (input : Input object) where
  | allInside
      (supportSubset : ∀ vertex ∈ input.path.support,
        vertex ∈ deletedWindowVertices object)
  | firstTransition
      (hit : Core.FiniteSearch.FirstHit input.edgeOrder
        input.TransitionAt)
      (crossing : OrientedCrossing input hit)
      (stub : BoundaryStub object)
      (stubExact : stub = crossing.boundaryStub)
      (endpoint : OutsideVertex object)
      (endpointExact : endpoint = stub.endpoint)
      (component : (outsideObject object).graph.ConnectedComponent)
      (componentExact : component = InducedPathColdSkeleton.component stub)

/-- Execute the exact local edge-index scan. -/
noncomputable def run {object : FiniteObject V} (input : Input object) :
    Result input := by
  cases equation : input.scan with
  | found hit =>
      let crossing := OrientedCrossing.ofFirstHit (hit := hit)
      let stub := crossing.boundaryStub
      exact .firstTransition hit crossing stub rfl stub.endpoint rfl
        (InducedPathColdSkeleton.component stub) rfl
  | absent none =>
      exact .allInside (input.support_subset_of_no_transition none)

theorem run_exhaustive {object : FiniteObject V} (input : Input object) :
    (∃ supportSubset, run input = .allInside supportSubset) ∨
    (∃ hit crossing stub stubExact endpoint endpointExact component componentExact,
      run input = .firstTransition hit crossing stub stubExact endpoint
        endpointExact component componentExact) := by
  cases equation : run input with
  | allInside supportSubset => exact Or.inl ⟨supportSubset, rfl⟩
  | firstTransition hit crossing stub stubExact endpoint endpointExact
      component componentExact =>
      exact Or.inr ⟨hit, crossing, stub, stubExact, endpoint, endpointExact,
        component, componentExact, rfl⟩

/-- The visible local ledger.  The first term computes the thirteen degree
tests for every selected window against the declared ambient vertex schedule;
the second records the cubic flags; the third performs two finite
`WindowIndex × Fin 13` membership scans at every supplied path edge. -/
noncomputable def visibleChecks {object : FiniteObject V}
    (input : Input object) : Nat :=
  13 * packingNumber object * object.input.vertices.card +
    13 * packingNumber object +
    26 * packingNumber object * input.path.length

theorem visibleChecks_eq {object : FiniteObject V} (input : Input object) :
    visibleChecks input =
      13 * packingNumber object * object.input.vertices.card +
        13 * packingNumber object +
        26 * packingNumber object * input.path.length := rfl

/-- Conservative locally polynomial bound.  It uses only the disjoint
selected-window packing bound and a supplied bound on this one path length. -/
theorem visibleChecks_le_square_add_linear
    {object : FiniteObject V} (input : Input object) (scale : Nat)
    (lengthBound : input.path.length ≤ scale) :
    visibleChecks input ≤ object.input.vertices.card ^ 2 +
      (2 * scale + 1) * object.input.vertices.card := by
  have packed := InducedPathPacking.packing_vertices_bound object 13
    (by decide)
  change 13 * packingNumber object ≤ object.input.vertices.card at packed
  unfold visibleChecks
  nlinarith

end StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition
