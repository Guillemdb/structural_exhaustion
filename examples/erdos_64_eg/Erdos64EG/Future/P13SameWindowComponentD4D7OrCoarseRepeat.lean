import Erdos64EG.Future.P13SameWindowComponentD1D3Ledger
import StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat
import StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [175]: D4--D7 reconstruction or coarse-repeat consumer

This thin adapter executes the generic graph consumer on the exact generic
node-174 result and proves agreement with the specialized node-174 run.  A
coarse repeat remains a CT10/refinement residual.  The bounded branch scans
only the actual stored rows and returns complete reconstruction or the first
exact missing row; with the current graph clauses it honestly takes the latter.
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

namespace P13SameWindowFirstTransitionBoundaryInput

variable (transition : P13SameWindowFirstTransitionBoundaryInput computed)
variable (source174 : P13SameWindowComponentD1D3LedgerSource transition)

abbrev D4D7GraphSource :=
  InducedPathComponentD4D7OrCoarseRepeat.Source
    (d1d3LedgerInput transition source174) source174.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable

end P13SameWindowFirstTransitionBoundaryInput

/-- The source retains both the generic exact result (including `codesNodup`)
and its literal specialization to the actual P13 node-174 execution. -/
structure P13SameWindowComponentD4D7OrCoarseRepeatSource
    (transition : P13SameWindowFirstTransitionBoundaryInput computed)
    (source174 : P13SameWindowComponentD1D3LedgerSource transition) where
  graphSource : transition.D4D7GraphSource source174
  node174Exact : transition.specializeD1D3LedgerOutput source174
    graphSource.node174 = transition.runD1D3Ledger source174

noncomputable def computedP13SameWindowComponentD4D7OrCoarseRepeatSource
    (transition : P13SameWindowFirstTransitionBoundaryInput computed)
    (source174 : P13SameWindowComponentD1D3LedgerSource transition) :
    P13SameWindowComponentD4D7OrCoarseRepeatSource transition source174 where
  graphSource :=
    InducedPathComponentD4D7OrCoarseRepeat.computedSource
      (transition.d1d3LedgerInput source174) source174.node173.value
        PowerOfTwoLength powerOfTwoLengthDecidable
  node174Exact := by
    apply congrArg (transition.specializeD1D3LedgerOutput source174)
    exact InducedPathComponentD4D7OrCoarseRepeat.source_exact
      (transition.d1d3LedgerInput source174) source174.node173.value
        PowerOfTwoLength powerOfTwoLengthDecidable _

namespace P13SameWindowFirstTransitionBoundaryInput

variable (transition : P13SameWindowFirstTransitionBoundaryInput computed)
variable (source174 : P13SameWindowComponentD1D3LedgerSource transition)
variable (source175 :
  P13SameWindowComponentD4D7OrCoarseRepeatSource transition source174)

abbrev D4D7GraphResult :=
  InducedPathComponentD4D7OrCoarseRepeat.Result
    (d1d3LedgerInput transition source174) source174.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable

abbrev D4D7CoarseRepeatResidual :=
  InducedPathComponentD4D7OrCoarseRepeat.CoarseRepeatResidual
    (d1d3LedgerInput transition source174) source174.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable

abbrev D4D7ReconstructedFamily :=
  InducedPathComponentD4D7OrCoarseRepeat.ReconstructedFamily
    (d1d3LedgerInput transition source174)

abbrev D4D7FirstMissingReconstruction :=
  InducedPathComponentD4D7OrCoarseRepeat.FirstMissingReconstruction
    (d1d3LedgerInput transition source174)

structure D4D7RoutedCoarseRepeat where
  residual : transition.D4D7CoarseRepeatResidual source174
  consumer : CT10.ExecutionResult
    (Routes.InducedPathComponentD4D7ToCT10.coarseCapability _ residual)
    (Routes.InducedPathComponentD4D7ToCT10.coarseInput _
      ctx.toBranchContext residual)
  consumerExact : consumer =
    Routes.InducedPathComponentD4D7ToCT10.coarseExecution _
      ctx.toBranchContext residual

structure D4D7RoutedFirstMissing where
  residual : transition.D4D7FirstMissingReconstruction source174
  consumer : CT10.ExecutionResult
    (Routes.InducedPathComponentD4D7ToCT10.missingCapability _ residual)
    (Routes.InducedPathComponentD4D7ToCT10.missingInput _
      ctx.toBranchContext residual)
  consumerExact : consumer =
    Routes.InducedPathComponentD4D7ToCT10.missingExecution _
      ctx.toBranchContext residual

structure D4D7BoundedResidual where
  graph : InducedPathComponentD4D7OrCoarseRepeat.BoundedResidual
    (d1d3LedgerInput transition source174) source174.node173.value
      PowerOfTwoLength powerOfTwoLengthDecidable
  lengthLeQbase :
    (InducedPathComponentBoundarySchedule.incidentStubs
      transition.graphInput).length ≤ p13ColdD1D3BaseThreshold

inductive D4D7OrCoarseRepeatOutput where
  | coarseRepeat (routed : transition.D4D7RoutedCoarseRepeat source174)
  | boundedReconstructed
      (bounded : transition.D4D7BoundedResidual source174)
      (family : transition.D4D7ReconstructedFamily source174)
  | boundedFirstMissing
      (bounded : transition.D4D7BoundedResidual source174)
      (routed : transition.D4D7RoutedFirstMissing source174)

/-- Execute the generic graph node-175 runner and only specialize its bounded
cardinality statement to `Qbase`. -/
noncomputable def runD4D7OrCoarseRepeat :
    transition.D4D7OrCoarseRepeatOutput source174 := by
  cases graphResult : InducedPathComponentD4D7OrCoarseRepeat.run
      (d1d3LedgerInput transition source174) source174.node173.value
        PowerOfTwoLength powerOfTwoLengthDecidable source175.graphSource with
  | coarseRepeat residual => exact .coarseRepeat {
      residual := residual
      consumer :=
        Routes.InducedPathComponentD4D7ToCT10.coarseExecution _
          ctx.toBranchContext residual
      consumerExact := rfl
    }
  | boundedReconstructed bounded family =>
      apply D4D7OrCoarseRepeatOutput.boundedReconstructed
        { graph := bounded, lengthLeQbase := by
            rw [p13ColdD1D3BaseThreshold_eq_stateCard]
            exact bounded.lengthLe }
      exact family
  | boundedFirstMissing bounded residual =>
      apply D4D7OrCoarseRepeatOutput.boundedFirstMissing
        { graph := bounded, lengthLeQbase := by
            rw [p13ColdD1D3BaseThreshold_eq_stateCard]
            exact bounded.lengthLe }
      exact {
        residual := residual
        consumer :=
          Routes.InducedPathComponentD4D7ToCT10.missingExecution _
            ctx.toBranchContext residual
        consumerExact := rfl
      }

theorem d4d7Consumer_exact_generic_node174 :
    source175.graphSource.node174 =
      InducedPathComponentD1D3Ledger.run
        (d1d3LedgerInput transition source174) source174.node173.value
          PowerOfTwoLength powerOfTwoLengthDecidable :=
  source175.graphSource.node174Exact

theorem d4d7Consumer_exact_specialized_node174 :
    transition.specializeD1D3LedgerOutput source174
      source175.graphSource.node174 = transition.runD1D3Ledger source174 :=
  source175.node174Exact

theorem runD4D7OrCoarseRepeat_exhaustive :
    (∃ residual, transition.runD4D7OrCoarseRepeat source174 source175 =
        .coarseRepeat residual) ∨
      (∃ bounded family,
        transition.runD4D7OrCoarseRepeat source174 source175 =
          .boundedReconstructed bounded family) ∨
      (∃ bounded residual,
        transition.runD4D7OrCoarseRepeat source174 source175 =
          .boundedFirstMissing bounded residual) := by
  cases equation : transition.runD4D7OrCoarseRepeat source174 source175 with
  | coarseRepeat residual => exact Or.inl ⟨residual, rfl⟩
  | boundedReconstructed bounded family =>
      exact Or.inr (Or.inl ⟨bounded, family, rfl⟩)
  | boundedFirstMissing bounded residual =>
      exact Or.inr (Or.inr ⟨bounded, residual, rfl⟩)

theorem d4d7Consumer_visibleChecks_polynomial :
    InducedPathComponentD4D7OrCoarseRepeat.visibleChecks
        (d1d3LedgerInput transition source174) ≤
      InducedPathComponentD1D3Ledger.localScale
        (d1d3LedgerInput transition source174) :=
  InducedPathComponentD4D7OrCoarseRepeat.visibleChecks_polynomial
    (d1d3LedgerInput transition source174)

/-- Combined upper ledger for the graph classifier and either routed CT10
consumer. -/
theorem d4d7Consumer_totalVisibleChecks_polynomial :
    InducedPathComponentD4D7OrCoarseRepeat.visibleChecks
        (d1d3LedgerInput transition source174) +
      Routes.InducedPathComponentD4D7ToCT10.visibleChecks
        (d1d3LedgerInput transition source174) ≤
      3 * InducedPathComponentD1D3Ledger.localScale
        (d1d3LedgerInput transition source174) := by
  unfold InducedPathComponentD4D7OrCoarseRepeat.visibleChecks
    Routes.InducedPathComponentD4D7ToCT10.visibleChecks
    InducedPathComponentD1D3Ledger.localScale
  omega

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
