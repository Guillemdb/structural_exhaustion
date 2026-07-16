import StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition

namespace StructuralExhaustion.Examples.PackedSupportBoundaryTransition

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
A theorem-independent transfer of the packed-support boundary transition.
The source supplies one simple path ending at a stated position of one
ambient-cubic selected window.  The reusable graph runner, rather than this
example, discovers whether the whole path stays in the deleted union or its
first boundary transition.
-/

variable {V : Type u} {object : FiniteObject V}

structure Source (object : FiniteObject V) where
  start : V
  window : WindowIndex object
  position : Fin 13
  path : object.graph.Walk start (selectedWindow object window position)
  isPath : path.IsPath
  cubic : InducedPathColdLedger.AmbientCubic object window

namespace Source

noncomputable def input (source : Source object) :
    InducedPathColdSkeletonBoundaryTransition.Input object where
  start := source.start
  finish := selectedWindow object source.window source.position
  path := source.path
  isPath := source.isPath
  finalInside := by
    classical
    simp only [InducedPathColdSkeleton.deletedWindowVertices,
      Finset.mem_biUnion]
    refine ⟨source.window, Finset.mem_univ _, ?_⟩
    simp only [source.cubic, if_pos, InducedPathPacking.mem_support_iff]
    exact ⟨source.position, rfl⟩

noncomputable def result (source : Source object) :=
  InducedPathColdSkeletonBoundaryTransition.run source.input

theorem exhaustive (source : Source object) :
    (∃ supportSubset, source.result = .allInside supportSubset) ∨
    (∃ hit crossing stub stubExact endpoint endpointExact component componentExact,
      source.result = .firstTransition hit crossing stub stubExact endpoint
        endpointExact component componentExact) :=
  InducedPathColdSkeletonBoundaryTransition.run_exhaustive source.input

theorem local_work_bound (source : Source object) (scale : Nat)
    (lengthBound : source.path.length ≤ scale) :
    InducedPathColdSkeletonBoundaryTransition.visibleChecks source.input ≤
      object.input.vertices.card ^ 2 +
        (2 * scale + 1) * object.input.vertices.card :=
  InducedPathColdSkeletonBoundaryTransition.visibleChecks_le_square_add_linear
    source.input scale lengthBound

end Source

/-! The next two fixtures execute the two exhaustive branches. -/

/-- A selected ambient-cubic window position supplies a zero-edge path wholly
inside the deleted union. -/
structure InsidePoint (object : FiniteObject V) where
  window : WindowIndex object
  position : Fin 13
  cubic : InducedPathColdLedger.AmbientCubic object window

namespace InsidePoint

noncomputable def source (point : InsidePoint object) : Source object where
  start := selectedWindow object point.window point.position
  window := point.window
  position := point.position
  path := .nil
  isPath := by simp
  cubic := point.cubic

theorem run_allInside (point : InsidePoint object) :
    ∃ supportSubset, point.source.result = .allInside supportSubset := by
  rcases point.source.exhaustive with allInside | transition
  · exact allInside
  · rcases transition with
      ⟨hit, _crossing, _stub, _stubExact, _endpoint, _endpointExact,
        _component, _componentExact, _runExact⟩
    have impossible : hit.value.1 < 0 := by
      simpa [Source.input, source] using hit.value.2
    omega

end InsidePoint

/-- One certified outside neighbour followed by an ambient-cubic window
position gives a literal one-edge first-transition fixture. -/
structure CrossingPoint (object : FiniteObject V) extends InsidePoint object where
  outside : V
  adjacent : object.graph.Adj outside
    (selectedWindow object window position)
  outside_not_deleted : outside ∉
    InducedPathColdSkeleton.deletedWindowVertices object

namespace CrossingPoint

noncomputable def source (point : CrossingPoint object) : Source object where
  start := point.outside
  window := point.window
  position := point.position
  path := .cons point.adjacent .nil
  isPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · simp
    · simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
      intro equal
      apply point.outside_not_deleted
      rw [equal]
      exact point.toInsidePoint.source.input.finalInside
  cubic := point.cubic

theorem run_firstTransition (point : CrossingPoint object) :
    ∃ hit crossing stub stubExact endpoint endpointExact component componentExact,
      point.source.result = .firstTransition hit crossing stub stubExact
        endpoint endpointExact component componentExact := by
  rcases point.source.exhaustive with allInside | transition
  · rcases allInside with ⟨supportSubset, _runExact⟩
    exact (point.outside_not_deleted
      (supportSubset point.outside point.source.input.path.start_mem_support)).elim
  · exact transition

end CrossingPoint

end StructuralExhaustion.Examples.PackedSupportBoundaryTransition
