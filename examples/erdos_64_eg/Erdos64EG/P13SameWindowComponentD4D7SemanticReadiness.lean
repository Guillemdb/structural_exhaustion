import Erdos64EG.P13SameWindowComponentD4D7OrCoarseRepeat
import StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdSkeleton

universe u

/-!
# Node [180]: exact component D4--D7 semantic-readiness fork

The full CT8 consumer is not dependency-ready: node 175 carries neither a
compatible-response family nor a smaller-object operation.  This node instead
eliminates the impossible reconstructed constructor and retains the exact
missing-D4--D7 witnesses on the two honest branches.  The stronger CT8 claim
must therefore remain a distinct successor.
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
variable (source175 :
  P13SameWindowComponentD4D7OrCoarseRepeatSource transition source174)

structure D4D7SemanticReadinessSource where
  node175 : transition.D4D7OrCoarseRepeatOutput source174
  node175Exact : node175 =
    transition.runD4D7OrCoarseRepeat source174 source175

noncomputable def computedD4D7SemanticReadinessSource :
    transition.D4D7SemanticReadinessSource source174 source175 where
  node175 := transition.runD4D7OrCoarseRepeat source174 source175
  node175Exact := rfl

structure D4D7CoarseSemanticBlock where
  routed : transition.D4D7RoutedCoarseRepeat source174
  firstMissing : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (InducedPathComponentD1D3Observation.data
      routed.residual.repetition.firstInput)
    routed.residual.repetition.firstPath)
  secondMissing : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (InducedPathComponentD1D3Observation.data
      routed.residual.repetition.secondInput)
    routed.residual.repetition.secondPath)

structure D4D7BoundedSemanticBlock where
  bounded : transition.D4D7BoundedResidual source174
  routed : transition.D4D7RoutedFirstMissing source174
  missing : Nonempty (TwoStubComponent.MissingD4D7Reconstruction
    (InducedPathComponentD1D3Observation.data
      (InducedPathComponentD1D3Ledger.connectorInput
        (transition.d1d3LedgerInput source174) routed.residual.scan.row))
    (InducedPathComponentD1D3Observation.canonicalPath
      (InducedPathComponentD1D3Ledger.connectorInput
        (transition.d1d3LedgerInput source174) routed.residual.scan.row)))

inductive D4D7SemanticReadinessOutput where
  | coarseBlocked
      (blocked : transition.D4D7CoarseSemanticBlock source174)
  | boundedBlocked
      (blocked : transition.D4D7BoundedSemanticBlock source174)

/-- Inspect exactly the retained node-175 constructor.  The complete-family
case is discharged by the graph-owned anchor-row impossibility theorem. -/
noncomputable def runD4D7SemanticReadiness
    (source180 : transition.D4D7SemanticReadinessSource source174 source175) :
    transition.D4D7SemanticReadinessOutput source174 := by
  cases source180.node175 with
  | coarseRepeat routed =>
      exact .coarseBlocked {
        routed := routed
        firstMissing := routed.residual.firstMissingD4D7
        secondMissing := routed.residual.secondMissingD4D7
      }
  | boundedReconstructed _bounded family =>
      exact (InducedPathComponentD4D7SemanticReadiness.reconstructed_impossible
        (transition.d1d3LedgerInput source174) family).elim
  | boundedFirstMissing bounded routed =>
      exact .boundedBlocked {
        bounded := bounded
        routed := routed
        missing := routed.residual.marker
      }

theorem d4d7SemanticReadiness_exact_node175
    (source180 : transition.D4D7SemanticReadinessSource source174 source175) :
    source180.node175 = transition.runD4D7OrCoarseRepeat source174 source175 :=
  source180.node175Exact

theorem runD4D7SemanticReadiness_exhaustive
    (source180 : transition.D4D7SemanticReadinessSource source174 source175) :
    (∃ blocked, transition.runD4D7SemanticReadiness source174 source175
      source180 = .coarseBlocked blocked) ∨
    (∃ blocked, transition.runD4D7SemanticReadiness source174 source175
      source180 = .boundedBlocked blocked) := by
  cases equation : transition.runD4D7SemanticReadiness source174 source175
      source180 with
  | coarseBlocked blocked => exact Or.inl ⟨blocked, rfl⟩
  | boundedBlocked blocked => exact Or.inr ⟨blocked, rfl⟩

theorem d4d7SemanticReadiness_visibleChecks_polynomial :
    InducedPathComponentD4D7SemanticReadiness.visibleChecks ≤
      InducedPathComponentD1D3Ledger.localScale
        (transition.d1d3LedgerInput source174) + 1 :=
  InducedPathComponentD4D7SemanticReadiness.visibleChecks_linear
    (transition.d1d3LedgerInput source174)

theorem exists_verifiedD4D7SemanticReadinessPrefix :
    ∃ output, output = transition.runD4D7SemanticReadiness source174 source175
      (transition.computedD4D7SemanticReadinessSource source174 source175) ∧
      ((∃ blocked, output = .coarseBlocked blocked) ∨
        (∃ blocked, output = .boundedBlocked blocked)) := by
  refine ⟨_, rfl, ?_⟩
  exact transition.runD4D7SemanticReadiness_exhaustive source174 source175 _

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
