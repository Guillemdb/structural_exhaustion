import Erdos64EG.P13FixedSkeletonEntrySchedule
import Erdos64EG.P13SelectedWindowCorridor
import StructuralExhaustion.Graph.InducedPathColdBranchExcess

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger
open StructuralExhaustion.Graph.InducedPathColdLedger
open StructuralExhaustion.Graph.InducedPathColdBranchExcess

universe u

/-!
# Fixed-skeleton branch-excess corridor schedule

This is the graph-owned implementation of the manuscript step following the
exact `15 - 2 = 13` cold-window calculation.  It filters the exact CT12 window
order to ambient-cubic windows, selects all thirteen literal branch-excess
half-edges of each retained window, and executes the canonical deleted-edge
first-failure corridor on every selected half-edge.

No cold family, outcome tag, path, context, or state collection is accepted
from a caller.  The only input is the verified node-`[21]` predecessor, used
for provenance; every schedule below is recomputed from its selected graph.
-/

abbrev P13AmbientCubicWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {window : WindowIndex ctx.G.object // AmbientCubic ctx.G.object window}

/-- Exact order-preserving ambient-cubic filter of the CT12 window schedule. -/
@[implicit_reducible]
noncomputable def p13AmbientCubicWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    FinEnum (P13AmbientCubicWindow ctx) :=
  Core.Enumeration.subtype (windowIndices ctx.G.object)
    (AmbientCubic ctx.G.object) (ambientCubicDecidable ctx.G.object)

/-- One literal selected excess half-edge and its computed first-failure
corridor, all tied to the same ambient-cubic window. -/
structure P13BranchExcessCorridor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) where
  stub : InducedPathColdCorridor.CubicStub ctx.G.object
  selected : stub ∈ branchExcessStubs ctx.G.object window.1 window.2
  result : P13SelectedWindowFirstFailure ctx stub
  resultExact : result = InducedPathColdCorridor.runFirstFailure
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable stub

/-- Run the paper's corridor classifier on all thirteen selected excess
half-edges of one ambient-cubic window. -/
noncomputable def p13WindowBranchExcessCorridors
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    List (P13BranchExcessCorridor ctx window) :=
  (branchExcessStubs ctx.G.object window.1 window.2).attach.map fun stub =>
    { stub := stub.1
      selected := stub.2
      result := InducedPathColdCorridor.runFirstFailure
        (p13SelectedWindowCorridorProducer ctx)
        PowerOfTwoLength powerOfTwoLengthDecidable stub.1
      resultExact := rfl }

theorem p13WindowBranchExcessCorridors_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowBranchExcessCorridors ctx window).length = 13 := by
  rw [p13WindowBranchExcessCorridors, List.length_map, List.length_attach,
    branchExcessStubs_length_eq_thirteen]

theorem P13BranchExcessCorridor.sameWindow
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) :
    corridor.stub.window = window.1 :=
  branchExcessStubs_same_window ctx.G.object window.1 window.2
    corridor.stub corridor.selected

/-- Global selected-half-edge schedule in the inherited cubic-window order. -/
noncomputable def p13BranchExcessCorridors
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (Sigma fun window : P13AmbientCubicWindow ctx =>
      P13BranchExcessCorridor ctx window) :=
  (p13AmbientCubicWindows ctx).orderedValues.flatMap fun window =>
    (p13WindowBranchExcessCorridors ctx window).map fun corridor =>
      ⟨window, corridor⟩

/-- There are exactly thirteen computed corridor entries per retained
ambient-cubic window. -/
set_option maxHeartbeats 800000 in
theorem p13BranchExcessCorridors_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessCorridors ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  let windows := (p13AmbientCubicWindows ctx).orderedValues
  change (windows.flatMap fun window =>
      (p13WindowBranchExcessCorridors ctx window).map fun corridor =>
        ⟨window, corridor⟩).length =
    13 * (p13AmbientCubicWindows ctx).card
  rw [← FinEnum.orderedValues_length]
  change (windows.flatMap fun window =>
      (p13WindowBranchExcessCorridors ctx window).map fun corridor =>
        ⟨window, corridor⟩).length = 13 * windows.length
  induction windows with
  | nil => rfl
  | cons window rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        p13WindowBranchExcessCorridors_length, List.length_cons]
      omega

/-- Node-`[21]` provenance wrapper.  The corridor list is deliberately not a
field and therefore cannot be supplied by an application. -/
structure VerifiedP13BranchExcessCorridorPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  previousExact : previous = node21

def verifiedP13BranchExcessCorridorPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    VerifiedP13BranchExcessCorridorPrefix ctx node21 := ⟨node21, rfl⟩

namespace VerifiedP13BranchExcessCorridorPrefix

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable def corridors
    (_prefix : VerifiedP13BranchExcessCorridorPrefix ctx node21) :=
  p13BranchExcessCorridors ctx

theorem corridors_length
    (verified : VerifiedP13BranchExcessCorridorPrefix ctx node21) :
    verified.corridors.length = 13 * (p13AmbientCubicWindows ctx).card :=
  p13BranchExcessCorridors_length ctx

end VerifiedP13BranchExcessCorridorPrefix

end Erdos64EG.Internal
