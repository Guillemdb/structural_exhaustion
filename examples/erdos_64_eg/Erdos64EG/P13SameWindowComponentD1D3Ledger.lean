import Erdos64EG.P13SameWindowComponentD1D3Observation
import Erdos64EG.P13SameWindowBaseScaleSplit
import StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [174]: cyclic component D1--D3 ledger and coarse collision

This thin adapter consumes the exact node-170 first-transition schedule and a
typed node-173 residual proved equal to the actual node-173 run.  The anchor
row is projected from that retained residual; every other row is computed by
re-anchoring the exact node-170 schedule.  It then performs only deterministic
coarse-code collision.  Full CT8 response comparison and removal remain
downstream.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}
variable {computed : P13SameWindowComputedNormalizedReturnBoundary input}

/-- Exact predecessor wrapper: node 174 cannot be run without retaining the
typed node-173 result and its equality to the actual node-173 computation. -/
structure P13SameWindowComponentD1D3LedgerSource
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) where
  node173 : P13SameWindowComponentD1D3Residual transition
  node173Exact : node173 = runP13SameWindowComponentD1D3Observation transition

/-- Canonical predecessor wrapper built directly from the computed node-173
run.  Callers following the verified chain need supply no fresh state. -/
noncomputable def computedP13SameWindowComponentD1D3LedgerSource
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    P13SameWindowComponentD1D3LedgerSource transition where
  node173 := runP13SameWindowComponentD1D3Observation transition
  node173Exact := rfl

namespace P13SameWindowFirstTransitionBoundaryInput

variable (transition : P13SameWindowFirstTransitionBoundaryInput computed)
variable (source : P13SameWindowComponentD1D3LedgerSource transition)

noncomputable def d1d3LedgerInput :
    InducedPathComponentD1D3Ledger.Input ctx.G.object where
  base := by
    let _retainedNode173 := source.node173
    exact transition.graphInput
  notBridge := fun stub _member => dart_not_bridge ctx
    (InducedPathColdCorridor.CubicStub.dart
      { token := stub.token, cubic := stub.cubic })

abbrev D1D3LedgerRepetition :=
  InducedPathComponentD1D3Ledger.Repetition
    (d1d3LedgerInput transition source) source.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable

/-- P13-specialized result with the bounded branch stated at `Qbase`. -/
inductive D1D3LedgerOutput where
  | repeated (repetition : transition.D1D3LedgerRepetition source)
  | bounded (codesNodup :
      ((InducedPathComponentD1D3Ledger.rows
        (d1d3LedgerInput transition source) source.node173.value
          PowerOfTwoLength powerOfTwoLengthDecidable).map Prod.snd).Nodup)
      (lengthLe :
      (InducedPathComponentBoundarySchedule.incidentStubs
        transition.graphInput).length ≤ p13ColdD1D3BaseThreshold)

noncomputable def specializeD1D3LedgerOutput
    (result : InducedPathComponentD1D3Ledger.Result
      (d1d3LedgerInput transition source) source.node173.value
        PowerOfTwoLength powerOfTwoLengthDecidable) :
    transition.D1D3LedgerOutput source := by
  cases result with
  | repeated repetition => exact .repeated repetition
  | bounded codesNodup lengthLe =>
      apply D1D3LedgerOutput.bounded codesNodup
      rw [p13ColdD1D3BaseThreshold_eq_stateCard]
      exact lengthLe

noncomputable def runD1D3Ledger : transition.D1D3LedgerOutput source :=
  transition.specializeD1D3LedgerOutput source
    (InducedPathComponentD1D3Ledger.run
      (d1d3LedgerInput transition source) source.node173.value
        PowerOfTwoLength powerOfTwoLengthDecidable)

theorem runD1D3Ledger_exhaustive :
    (∃ repetition, transition.runD1D3Ledger source = .repeated repetition) ∨
      (∃ codesNodup lengthLe,
        transition.runD1D3Ledger source = .bounded codesNodup lengthLe) := by
  cases equation : transition.runD1D3Ledger source with
  | repeated repetition => exact Or.inl ⟨repetition, rfl⟩
  | bounded codesNodup lengthLe =>
      exact Or.inr ⟨codesNodup, lengthLe, rfl⟩

theorem d1d3Ledger_exact_node170_schedule :
    (d1d3LedgerInput transition source).base = transition.graphInput := rfl

theorem d1d3Ledger_source_exact_node173 :
    source.node173 = runP13SameWindowComponentD1D3Observation transition :=
  source.node173Exact

theorem d1d3Ledger_true_cyclic_successor
    (stub : InducedPathComponentD1D3Ledger.Stub
      (d1d3LedgerInput transition source)) :
    InducedPathComponentBoundarySchedule.successor
        (InducedPathComponentD1D3Ledger.connectorInput
          (d1d3LedgerInput transition source) stub) =
      @List.next _
        (InducedPathComponentBoundarySchedule.boundaryStubs
          ctx.G.object).decEq
        (InducedPathComponentBoundarySchedule.incidentStubs
          transition.graphInput) stub.1 stub.2 :=
  InducedPathComponentD1D3Ledger.connector_successor_eq
    (d1d3LedgerInput transition source) stub

/-- The anchor row is definitionally projected from the retained node-173
residual, rather than recomputed from node 170. -/
theorem d1d3Ledger_anchor_row_eq_retained :
    InducedPathComponentD1D3Ledger.rowState
      (d1d3LedgerInput transition source) source.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable
      (InducedPathComponentD1D3Ledger.anchorStub
        (d1d3LedgerInput transition source)) = source.node173.value :=
  InducedPathComponentD1D3Ledger.rowState_anchor
    (d1d3LedgerInput transition source) source.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable

theorem d1d3Ledger_retained_anchor_agrees_actual_node173 :
    source.node173.value =
      (runP13SameWindowComponentD1D3Observation transition).value := by
  exact congrArg (fun residual => residual.value) source.node173Exact

theorem d1d3Ledger_visibleChecks_polynomial :
    InducedPathComponentD1D3Ledger.visibleChecks
        (d1d3LedgerInput transition source) ≤
      100 * InducedPathComponentD1D3Ledger.localScale
        (d1d3LedgerInput transition source) ^ 4 :=
  InducedPathComponentD1D3Ledger.visibleChecks_polynomial
    (d1d3LedgerInput transition source)

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
