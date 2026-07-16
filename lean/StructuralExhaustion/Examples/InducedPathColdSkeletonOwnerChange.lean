import StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange

namespace StructuralExhaustion.Examples.PackedSupportOwnerChange

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
A concrete one-edge transfer execution.  Two actual distinct ambient-cubic
selected windows and one supplied graph edge between their stated positions
form a two-vertex all-inside path.  The exact reusable runner must return its
first-cross-window constructor at the sole edge.
-/

structure CrossWindowEdge (object : FiniteObject V) where
  leftWindow : WindowIndex object
  rightWindow : WindowIndex object
  distinct : leftWindow ≠ rightWindow
  leftPosition : Fin 13
  rightPosition : Fin 13
  leftCubic : InducedPathColdLedger.AmbientCubic object leftWindow
  rightCubic : InducedPathColdLedger.AmbientCubic object rightWindow
  adjacent : object.graph.Adj
    (selectedWindow object leftWindow leftPosition)
    (selectedWindow object rightWindow rightPosition)

namespace CrossWindowEdge

noncomputable def boundaryInput (edge : CrossWindowEdge object) :
    InducedPathColdSkeletonBoundaryTransition.Input object where
  start := selectedWindow object edge.leftWindow edge.leftPosition
  finish := selectedWindow object edge.rightWindow edge.rightPosition
  path := .cons edge.adjacent .nil
  isPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · simp
    · simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
      intro equal
      have sameVertex : selectedWindow object edge.leftWindow edge.leftPosition =
          selectedWindow object edge.rightWindow edge.rightPosition := equal
      let leftSlot : InducedPathColdSkeletonOwnerChange.OwnedSlot object
          (selectedWindow object edge.leftWindow edge.leftPosition) :=
        ⟨edge.leftWindow, edge.leftCubic, edge.leftPosition, rfl⟩
      let rightSlot : InducedPathColdSkeletonOwnerChange.OwnedSlot object
          (selectedWindow object edge.leftWindow edge.leftPosition) :=
        ⟨edge.rightWindow, edge.rightCubic, edge.rightPosition,
          sameVertex.symm⟩
      exact edge.distinct (leftSlot.window_unique rightSlot)
  finalInside := by
    classical
    simp only [InducedPathColdSkeleton.deletedWindowVertices,
      Finset.mem_biUnion]
    refine ⟨edge.rightWindow, Finset.mem_univ _, ?_⟩
    simp only [edge.rightCubic, if_pos,
      InducedPathPacking.mem_support_iff]
    exact ⟨edge.rightPosition, rfl⟩

theorem support_inside (edge : CrossWindowEdge object) :
    ∀ vertex ∈ edge.boundaryInput.path.support,
      vertex ∈ InducedPathColdSkeleton.deletedWindowVertices object := by
  classical
  intro vertex member
  simp only [boundaryInput, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, List.mem_cons] at member
  rcases member with rfl | member
  · simp only [InducedPathColdSkeleton.deletedWindowVertices,
      Finset.mem_biUnion]
    refine ⟨edge.leftWindow, Finset.mem_univ _, ?_⟩
    simp only [edge.leftCubic, if_pos,
      InducedPathPacking.mem_support_iff]
    exact ⟨edge.leftPosition, rfl⟩
  · rcases member with rfl | impossible
    · exact edge.boundaryInput.finalInside
    · simp at impossible

noncomputable def input (edge : CrossWindowEdge object) :
    InducedPathColdSkeletonOwnerChange.Input object :=
  InducedPathColdSkeletonOwnerChange.Input.prepare edge.boundaryInput
    edge.support_inside

theorem run_firstCrossWindow (edge : CrossWindowEdge object) :
    ∃ table hit crossing,
      InducedPathColdSkeletonOwnerChange.run edge.input =
        .firstCrossWindow table hit crossing := by
  rcases InducedPathColdSkeletonOwnerChange.run_exhaustive edge.input with
    single | crossing
  · rcases single with ⟨_table, owner, cubic, supportSubset, _runExact⟩
    have leftMember := supportSubset
      (selectedWindow object edge.leftWindow edge.leftPosition)
      edge.input.path.start_mem_support
    have rightMember := supportSubset
      (selectedWindow object edge.rightWindow edge.rightPosition)
      edge.input.path.end_mem_support
    rcases (InducedPathPacking.mem_support_iff object 13
      (selectedWindow object owner) _).1 leftMember with ⟨lp, leq⟩
    rcases (InducedPathPacking.mem_support_iff object 13
      (selectedWindow object owner) _).1 rightMember with ⟨rp, req⟩
    let ownerLeft : InducedPathColdSkeletonOwnerChange.OwnedSlot object
        (selectedWindow object edge.leftWindow edge.leftPosition) :=
      ⟨owner, cubic, lp, leq⟩
    let left : InducedPathColdSkeletonOwnerChange.OwnedSlot object
        (selectedWindow object edge.leftWindow edge.leftPosition) :=
      ⟨edge.leftWindow, edge.leftCubic, edge.leftPosition, rfl⟩
    let ownerRight : InducedPathColdSkeletonOwnerChange.OwnedSlot object
        (selectedWindow object edge.rightWindow edge.rightPosition) :=
      ⟨owner, cubic, rp, req⟩
    let right : InducedPathColdSkeletonOwnerChange.OwnedSlot object
        (selectedWindow object edge.rightWindow edge.rightPosition) :=
      ⟨edge.rightWindow, edge.rightCubic, edge.rightPosition, rfl⟩
    have leftEq : owner = edge.leftWindow := ownerLeft.window_unique left
    have rightEq : owner = edge.rightWindow := ownerRight.window_unique right
    exact (edge.distinct (leftEq.symm.trans rightEq)).elim
  · exact crossing

/-- The one-edge fixture pins the sole hit and every graph-owned projection
of the returned crossing. -/
theorem run_firstCrossWindow_exact (edge : CrossWindowEdge object) :
    ∃ table hit crossing,
      InducedPathColdSkeletonOwnerChange.run edge.input =
        .firstCrossWindow table hit crossing ∧
      hit.value.1 = 0 ∧
      crossing.leftSlot.window = edge.leftWindow ∧
      crossing.leftSlot.position = edge.leftPosition ∧
      crossing.rightSlot.window = edge.rightWindow ∧
      crossing.rightSlot.position = edge.rightPosition ∧
      edge.input.path.getVert hit.value.1 =
        selectedWindow object edge.leftWindow edge.leftPosition ∧
      edge.input.path.getVert (hit.value.1 + 1) =
        selectedWindow object edge.rightWindow edge.rightPosition ∧
      crossing.leftToken.1 = edge.leftWindow ∧
      crossing.leftToken.2.2.1 =
        selectedWindow object edge.rightWindow edge.rightPosition ∧
      tokenSubtype object crossing.leftToken = .crossWindow ∧
      crossing.rightToken.1 = edge.rightWindow ∧
      crossing.rightToken.2.2.1 =
        selectedWindow object edge.leftWindow edge.leftPosition ∧
      tokenSubtype object crossing.rightToken = .crossWindow := by
  rcases edge.run_firstCrossWindow with ⟨table, hit, crossing, runExact⟩
  have hitZero : hit.value.1 = 0 := by
    have bound := hit.value.2
    change hit.value.1 < edge.input.path.length at bound
    simpa [input, boundaryInput] using bound
  have leftVertex : edge.input.path.getVert hit.value.1 =
      selectedWindow object edge.leftWindow edge.leftPosition := by
    rw [hitZero]
    change (SimpleGraph.Walk.cons edge.adjacent SimpleGraph.Walk.nil).getVert 0 = _
    simp [input, boundaryInput]
  have rightVertex : edge.input.path.getVert (hit.value.1 + 1) =
      selectedWindow object edge.rightWindow edge.rightPosition := by
    rw [hitZero]
    change (SimpleGraph.Walk.cons edge.adjacent SimpleGraph.Walk.nil).getVert 1 = _
    simp
  let expectedLeft : InducedPathColdSkeletonOwnerChange.OwnedSlot object
      (edge.input.path.getVert hit.value.1) :=
    ⟨edge.leftWindow, edge.leftCubic, edge.leftPosition, leftVertex.symm⟩
  let expectedRight : InducedPathColdSkeletonOwnerChange.OwnedSlot object
      (edge.input.path.getVert (hit.value.1 + 1)) :=
    ⟨edge.rightWindow, edge.rightCubic, edge.rightPosition, rightVertex.symm⟩
  have leftWindow := crossing.leftSlot.window_unique expectedLeft
  have rightWindow := crossing.rightSlot.window_unique expectedRight
  have leftPosition := crossing.leftSlot.position_unique expectedLeft leftWindow
  have rightPosition := crossing.rightSlot.position_unique expectedRight rightWindow
  refine ⟨table, hit, crossing, runExact, hitZero, leftWindow, leftPosition,
    rightWindow, rightPosition, leftVertex, rightVertex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact crossing.leftTokenWindow.trans leftWindow
  · exact crossing.leftTokenNeighbor.trans rightVertex
  · exact crossing.leftTokenSubtype
  · exact crossing.rightTokenWindow.trans rightWindow
  · exact crossing.rightTokenNeighbor.trans leftVertex
  · exact crossing.rightTokenSubtype

theorem exact_local_work (edge : CrossWindowEdge object) :
    InducedPathColdSkeletonOwnerChange.visibleChecks edge.input ≤
      object.input.vertices.card ^ 2 +
        2 * (object.input.vertices.card + 1) := by
  apply InducedPathColdSkeletonOwnerChange.visibleChecks_le edge.input 2
  change edge.boundaryInput.path.support.length ≤ 2
  simp [boundaryInput]

end CrossWindowEdge

end StructuralExhaustion.Examples.PackedSupportOwnerChange
