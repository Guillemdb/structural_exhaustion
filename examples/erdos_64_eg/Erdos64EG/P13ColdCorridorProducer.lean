import Erdos64EG.CT2BridgeContraction
import Erdos64EG.P13HotColdInterface
import StructuralExhaustion.Graph.InducedPathColdCorridor

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u uCoordinate uState

/-!
# Concrete node-153 corridor producer

This adapter starts from classifier-produced cold windows and literal
external-neighbour incidences.  The bridge-reduction prefix supplies the
non-bridge theorem, so the framework constructs the return corridor and runs
the first-failure scan.  No corridor, germ, or outcome is accepted as input.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- The list-selected CT12 window and the window-ledger index are the same
maximum-packing member, with list membership converted to finset membership. -/
noncomputable def selectedWindowIndex (window : SelectedP13Window ctx) :
    WindowIndex ctx.G.object := by
  classical
  refine ⟨window.1, ?_⟩
  change window.1 ∈
    (Graph.InducedPathPacking.windows ctx.G.object 13 (by decide)).toFinset
  exact List.mem_toFinset.mpr window.2

/-- One literal external stub of a classifier-produced cold window, together
with the computed ambient-cubic proof retained by node 151. -/
structure ClassifiedColdCubicStub
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) where
  cold : data.ColdWindow
  position : Fin 13
  neighbor : ctx.G.Vertex
  external : neighbor ∈ externalNeighbors ctx.G.object
    (selectedWindowIndex cold.window) position
  cubic : InducedPathColdLedger.AmbientCubic ctx.G.object
    (selectedWindowIndex cold.window)

namespace ClassifiedColdCubicStub

variable {data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous}

/-- Forget only the classifier evidence; the resulting graph stub still owns
the exact selected window, position, external endpoint, and cubic proof. -/
noncomputable def toGraphStub (stub : ClassifiedColdCubicStub data) :
    InducedPathColdCorridor.CubicStub ctx.G.object where
  token := ⟨selectedWindowIndex stub.cold.window,
    ⟨stub.position, ⟨stub.neighbor, stub.external⟩⟩⟩
  cubic := stub.cubic

end ClassifiedColdCubicStub

/-- The producer is obtained directly from the already verified CT2
bridgelessness theorem on the identical selected graph. -/
def p13ColdCorridorProducer :
    InducedPathColdCorridor.Producer ctx.G.object where
  notBridge := dart_not_bridge ctx

abbrev P13ColdFirstFailureResult
    {data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous}
    (stub : ClassifiedColdCubicStub data) :=
  InducedPathColdCorridor.FirstFailureResult p13ColdCorridorProducer
    PowerOfTwoLength powerOfTwoLengthDecidable stub.toGraphStub

/-- Execute node 153 from the exact cold external incidence. -/
noncomputable def runP13ColdFirstFailure
    {data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous}
    (stub : ClassifiedColdCubicStub data) :
    P13ColdFirstFailureResult stub :=
  InducedPathColdCorridor.runFirstFailure p13ColdCorridorProducer
    PowerOfTwoLength powerOfTwoLengthDecidable stub.toGraphStub

/-- Exact exhaustive output: a first dyadic/surplus event with clean prefix,
or the framework-constructed structural germ. -/
theorem runP13ColdFirstFailure_total
    {data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous}
    (stub : ClassifiedColdCubicStub data) :
    (∃ hit event,
      runP13ColdFirstFailure stub = .first hit event) ∨
    (∃ noEvent germ,
      runP13ColdFirstFailure stub = .germ noEvent germ) :=
  InducedPathColdCorridor.runFirstFailure_total p13ColdCorridorProducer
    PowerOfTwoLength powerOfTwoLengthDecidable stub.toGraphStub

/-- A quiet node-153 result has only an ambient-finite support bound.  This
is the exact formal boundary for the missing constant target-response code;
it cannot be silently promoted to `P13ColdGermLedger.ColdBoundedGerm`. -/
theorem structuralGerm_support_le_vertices
    {data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous}
    (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub) :
    (p13ColdCorridorProducer.ambientReturn stub.toGraphStub).support.length ≤
      ctx.G.object.input.vertices.card :=
  germ.supportBound

end Erdos64EG.Internal
