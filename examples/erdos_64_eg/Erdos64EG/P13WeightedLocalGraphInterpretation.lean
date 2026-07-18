import Erdos64EG.P13PartIWindowDensityTriage
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-! First graph-semantic obligation for one weighted hot package. -/

abbrev P13WeightedScheduledState
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :=
  {state : package.State // state ∈ package.states.values}

abbrev P13WeightedScheduledCoordinate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) :=
  {coordinate : package.Coordinate // coordinate ∈ package.coordinates.values}

/-- Exact missing producer.  The local graph completion owns one connector,
whereas a weighted state owns a connector separately at each retained
coordinate.  The minimal faithful adapter is therefore indexed by both the
scheduled state and scheduled coordinate. -/
structure P13WeightedLocalGraphInterpretation
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window) : Type (u + 1) where
  interpret : P13WeightedScheduledState package →
    P13WeightedScheduledCoordinate package →
      P13LocalGraphCompletion ctx window
  connectorExact : ∀ state coordinate slot,
    (interpret state coordinate).connector slot =
      package.connector state.1 coordinate.1 slot
  responseExact : ∀ state coordinate,
    p13LocalResponse (interpret state coordinate)
        (package.barrierIndex coordinate.1) =
      package.accepts coordinate.1 state.1

namespace P13WeightedLocalGraphInterpretation

theorem connector_mem_support
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    {package : P13WeightedLiveWindowPackage ctx node21 window}
    (interpretation : P13WeightedLocalGraphInterpretation package)
    (state : P13WeightedScheduledState package)
    (coordinate : P13WeightedScheduledCoordinate package) (slot : Fin 15) :
    package.connector state.1 coordinate.1 slot ∈
      (interpretation.interpret state coordinate).support := by
  rw [← interpretation.connectorExact state coordinate slot]
  exact (interpretation.interpret state coordinate).connectorSupported slot

theorem window_mem_support
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    {package : P13WeightedLiveWindowPackage ctx node21 window}
    (interpretation : P13WeightedLocalGraphInterpretation package)
    (state : P13WeightedScheduledState package)
    (coordinate : P13WeightedScheduledCoordinate package) (position : Fin 13) :
    window.1 position ∈ (interpretation.interpret state coordinate).support :=
  (interpretation.interpret state coordinate).windowSupported position

end P13WeightedLocalGraphInterpretation

/-- Honest residual: node [21] and the weighted ledger do not construct the
coordinate-indexed graph interpretation. -/
structure P13WeightedLocalGraphInterpretationRequirement
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {window : P13SelectedConnectorWindow ctx}
    (package : P13WeightedLiveWindowPackage ctx node21 window)
    extends Core.ExactHandoff node21 where
  missing : ¬Nonempty (P13WeightedLocalGraphInterpretation package)

end Erdos64EG.Internal
