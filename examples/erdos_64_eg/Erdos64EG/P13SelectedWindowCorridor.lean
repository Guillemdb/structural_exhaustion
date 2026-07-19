import Erdos64EG.CT2BridgeContraction
import Erdos64EG.P13MultiScaleConnectorState
import StructuralExhaustion.Graph.InducedPathColdStubSelection

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Graph-owned corridor entry for every selected P13 window

This bypasses the invalid actual-path Boolean classifier.  Every literal
CT12-selected window is classified directly from graph degrees.  A first
non-cubic position is an actual surplus handoff.  Otherwise the framework
selects the first external incidence from the fifteen-stub ledger, constructs
the deleted-edge return corridor from bridgelessness, and runs the existing
first-failure machine.
-/

noncomputable def selectedConnectorWindowIndex
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (window : P13SelectedConnectorWindow ctx) : WindowIndex ctx.G.object := by
  classical
  refine ⟨window.1, ?_⟩
  change window.1 ∈
    (Graph.InducedPathPacking.windows ctx.G.object 13 (by decide)).toFinset
  exact List.mem_toFinset.mpr window.2

def p13SelectedWindowCorridorProducer
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    InducedPathColdCorridor.Producer ctx.G.object where
  notBridge := minimality_dart_not_bridge ctx

abbrev P13SelectedWindowFirstFailure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (stub : InducedPathColdCorridor.CubicStub ctx.G.object) :=
  InducedPathColdCorridor.FirstFailureResult
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable stub

inductive P13SelectedWindowCorridorRoute
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) where
  | surplus (position : Fin 13)
      (high : 3 < ctx.G.object.degree (window.1 position))
  | corridor (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (result : P13SelectedWindowFirstFailure ctx stub)

/-- Complete graph-owned execution from one selected window. -/
noncomputable def routeSelectedWindowCorridor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) :
    P13SelectedWindowCorridorRoute ctx window :=
  match InducedPathColdStubSelection.classify ctx.G.object
      (fun vertex =>
        ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))
      (selectedConnectorWindowIndex window) with
  | .high position high => .surplus position high
  | .cubic stub same =>
      .corridor stub same
        (InducedPathColdCorridor.runFirstFailure
          (p13SelectedWindowCorridorProducer ctx)
          PowerOfTwoLength powerOfTwoLengthDecidable stub)

theorem routeSelectedWindowCorridor_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) :
    (∃ position high,
      routeSelectedWindowCorridor ctx window = .surplus position high) ∨
    (∃ stub same result,
      routeSelectedWindowCorridor ctx window = .corridor stub same result) := by
  cases equation : routeSelectedWindowCorridor ctx window with
  | surplus position high => exact Or.inl ⟨position, high, rfl⟩
  | corridor stub same result => exact Or.inr ⟨stub, same, result, rfl⟩

end Erdos64EG.Internal
