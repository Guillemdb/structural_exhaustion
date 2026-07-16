import Erdos64EG.P13SameWindowNormalizedReturnPackedSupportTransition
import StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Node [169]: first owner change on the all-inside return

This adapter consumes equality with node `[168]`'s computed `allInside`
constructor.  The reusable graph runner assigns the unique ambient-cubic
selected-window owner to every vertex of the same normalized return.  Its
single-window constructor is impossible because the return starts at the
original external stub neighbour and ends in that stub's selected window.

The surviving output is one exact first cross-window edge.  Both endpoints
remain in the packed union, so no cold-skeleton boundary stub or cold-family
membership is claimed.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {boundaryInput : P13SameWindowNormalizedBoundaryInput (short := short)}

/-- Exact node-`[168]` all-inside predecessor, indexed by the computed
node-`[167]` boundary. -/
structure P13SameWindowComputedAllInside
    (computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput) where
  supportSubset : ∀ vertex ∈ computed.graphInput.path.support,
    vertex ∈ InducedPathColdSkeleton.deletedWindowVertices ctx.G.object
  runExact : runP13SameWindowNormalizedReturnPackedSupportTransition computed =
    .allInside supportSubset

namespace P13SameWindowComputedAllInside

variable {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}

noncomputable def graphInput (inside : P13SameWindowComputedAllInside computed) :
    InducedPathColdSkeletonOwnerChange.Input ctx.G.object :=
  InducedPathColdSkeletonOwnerChange.Input.prepare computed.graphInput
    inside.supportSubset

theorem graphInput_support_bounded
    (inside : P13SameWindowComputedAllInside computed) :
    inside.graphInput.path.support.length ≤ p13ColdD1D3BaseThreshold := by
  change computed.graphInput.path.support.length ≤ p13ColdD1D3BaseThreshold
  have bounded := computed.support_bounded
  rw [SimpleGraph.Walk.length_support] at bounded ⊢
  rw [computed.graphInput_path_length]
  exact bounded

end P13SameWindowComputedAllInside

/-- Exact surviving node-`[169]` residual. -/
structure P13SameWindowFirstCrossWindow
    {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}
    (inside : P13SameWindowComputedAllInside computed) where
  table : InducedPathColdSkeletonOwnerChange.Input.OwnerTable inside.graphInput
  hit : Core.FiniteSearch.FirstHit inside.graphInput.edgeOrder
    (inside.graphInput.OwnerChangeAt table)
  crossing : InducedPathColdSkeletonOwnerChange.FirstCrossWindow
    inside.graphInput table hit
  runExact : InducedPathColdSkeletonOwnerChange.run inside.graphInput =
    .firstCrossWindow table hit crossing

private theorem singleWindow_impossible
    {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}
    (inside : P13SameWindowComputedAllInside computed)
    (owner : WindowIndex ctx.G.object)
    (cubic : InducedPathColdLedger.AmbientCubic ctx.G.object owner)
    (supportSubset : ∀ vertex ∈ inside.graphInput.path.support,
      vertex ∈ InducedPathPacking.support ctx.G.object 13
        (selectedWindow ctx.G.object owner)) : False := by
  classical
  have finishMember := supportSubset
    (selectedWindow ctx.G.object quiet.stub.window quiet.stub.position)
    inside.graphInput.path.end_mem_support
  rcases (InducedPathPacking.mem_support_iff ctx.G.object 13
    (selectedWindow ctx.G.object owner) _).1 finishMember with
    ⟨ownerPosition, ownerExact⟩
  let ownerSlot : InducedPathColdSkeletonOwnerChange.OwnedSlot ctx.G.object
      (selectedWindow ctx.G.object quiet.stub.window quiet.stub.position) := {
    window := owner
    cubic := cubic
    position := ownerPosition
    exact := ownerExact
  }
  let selectedSlot : InducedPathColdSkeletonOwnerChange.OwnedSlot ctx.G.object
      (selectedWindow ctx.G.object quiet.stub.window quiet.stub.position) := {
    window := quiet.stub.window
    cubic := quiet.stub.cubic
    position := quiet.stub.position
    exact := rfl
  }
  have sameOwner : owner = quiet.stub.window :=
    ownerSlot.window_unique selectedSlot
  have startMember := supportSubset quiet.stub.neighbor
    inside.graphInput.path.start_mem_support
  rw [sameOwner] at startMember
  exact (token_neighbor_not_mem_own_support ctx.G.object quiet.stub.token)
    startMember

/-- Execute the generic owner scan and eliminate only its impossible
single-window constructor. -/
noncomputable def runP13SameWindowPackedOwnerChange
    {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}
    (inside : P13SameWindowComputedAllInside computed) :
    P13SameWindowFirstCrossWindow inside := by
  generalize equation : InducedPathColdSkeletonOwnerChange.run
    inside.graphInput = result
  cases result with
  | singleWindow table owner cubic supportSubset =>
      exact (singleWindow_impossible inside owner cubic supportSubset).elim
  | firstCrossWindow table hit crossing =>
      exact ⟨table, hit, crossing, equation⟩

theorem runP13SameWindowPackedOwnerChange_exact
    {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}
    (inside : P13SameWindowComputedAllInside computed) :
    InducedPathColdSkeletonOwnerChange.run inside.graphInput =
      .firstCrossWindow (runP13SameWindowPackedOwnerChange inside).table
        (runP13SameWindowPackedOwnerChange inside).hit
        (runP13SameWindowPackedOwnerChange inside).crossing :=
  (runP13SameWindowPackedOwnerChange inside).runExact

/-- Node-local work: one scan of at most thirteen slots per selected window
for every vertex of the supplied return, followed by one owner comparison per
return edge. -/
theorem p13SameWindowPackedOwnerChange_visibleChecks_le
    {computed : P13SameWindowComputedNormalizedReturnBoundary boundaryInput}
    (inside : P13SameWindowComputedAllInside computed) :
    InducedPathColdSkeletonOwnerChange.visibleChecks inside.graphInput ≤
      ctx.G.object.input.vertices.card ^ 2 +
        p13ColdD1D3BaseThreshold *
        (ctx.G.object.input.vertices.card + 1) :=
  InducedPathColdSkeletonOwnerChange.visibleChecks_le inside.graphInput
    p13ColdD1D3BaseThreshold inside.graphInput_support_bounded

end Erdos64EG.Internal
