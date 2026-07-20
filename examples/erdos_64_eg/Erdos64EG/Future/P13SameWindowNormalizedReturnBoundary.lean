import Erdos64EG.Future.P13SameWindowNonRootChordResolution
import Erdos64EG.Future.P13SameWindowOutsideBoundaryStar
import StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [167]: normalized one-return boundary rejoin

This thin adapter rejoins the exact computed node-`[165]` rejected-chord
return and node-`[166]` outside-boundary result.  It delegates to the generic
graph normalization, retaining one return, one outside incidence, cubic root
ownership, the inherited `Qbase` support bound, and branch-sensitive length
evidence.

No scan is performed here.  In particular, this node does not construct a
`BoundaryStub`, outside-vertex collection, component, successor, D4--D7
coordinate, CT3 input, density statement, or iteration/termination theorem.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}

/-- Exact node-`[165]` computation, indexed by its node-`[162]` chord input. -/
structure P13SameWindowComputedShorterBoundary
    (short : P13SameWindowComputedShort fork quiet) where
  branch : P13SameWindowComputedNonRootChord short
  result : P13SameWindowShorterReturn branch
  runExact : runP13SameWindowNonRootChordResolution branch = result

theorem P13SameWindowComputedShorterBoundary.result_exact
    (computed : P13SameWindowComputedShorterBoundary short) :
    computed.result =
      runP13SameWindowNonRootChordResolution computed.branch :=
  computed.runExact.symm

/-- The two precise predecessor outcomes accepted by node `[167]`. -/
inductive P13SameWindowNormalizedBoundaryInput
    (short : P13SameWindowComputedShort fork quiet) where
  | rejectedChord (computed : P13SameWindowComputedShorterBoundary short)
  | outsideBoundary
      (computed : P13SameWindowComputedOutsideBoundary short)

namespace P13SameWindowNormalizedBoundaryInput

/-- Exact graph-owned input assembled from either predecessor computation. -/
noncomputable def graphInput
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    DeletedEdgeReturnNormalizedBoundary.Input short.setup PowerOfTwoLength
      powerOfTwoLengthDecidable p13ColdD1D3BaseThreshold := by
  cases input with
  | rejectedChord computed =>
      let rejected : DeletedEdgeReturnNormalizedBoundary.RejectedChordRun
          short.setup PowerOfTwoLength powerOfTwoLengthDecidable := {
        input := computed.branch.genericInput
        lengthRejected := computed.result.lengthRejected
        shorter := computed.result.shorter
        shorterExact := computed.result.shorterExact
        strict := computed.result.strict
        runExact := computed.result.runExact
      }
      exact .rejectedChord rejected short.return_support_bounded
  | outsideBoundary computed =>
      exact .outsideBoundary computed.graphBranch
        short.return_support_bounded

end P13SameWindowNormalizedBoundaryInput

/-- Exact dependent node-`[167]` output. -/
abbrev P13SameWindowNormalizedReturnBoundary
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :=
  DeletedEdgeReturnNormalizedBoundary.NormalizedReturnBoundary input.graphInput

/-- Execute only the graph-owned proof transformation. -/
noncomputable def runP13SameWindowNormalizedReturnBoundary
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    P13SameWindowNormalizedReturnBoundary input :=
  DeletedEdgeReturnNormalizedBoundary.normalize input.graphInput

/-- The selected normalized support retains the exact inherited `Qbase`
bound on both branches. -/
theorem runP13SameWindowNormalizedReturnBoundary_support_bounded
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    (runP13SameWindowNormalizedReturnBoundary input).selectedReturn.path.support.length ≤
      p13ColdD1D3BaseThreshold :=
  (runP13SameWindowNormalizedReturnBoundary input).support_bound

/-- The selected return never exceeds the exact node-`[162]` return length. -/
theorem runP13SameWindowNormalizedReturnBoundary_length_le
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    (runP13SameWindowNormalizedReturnBoundary input).selectedReturn.path.length ≤
      short.setup.returnPath.path.length :=
  (runP13SameWindowNormalizedReturnBoundary input).length_le_original

/-- Every normalized result retains one literal outside adjacent endpoint. -/
theorem runP13SameWindowNormalizedReturnBoundary_outside
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    let result := runP13SameWindowNormalizedReturnBoundary input
    result.outsideVertex ∉ result.selectedReturn.path.support ∧
      ctx.G.object.graph.Adj quiet.stub.neighbor result.outsideVertex := by
  exact ⟨(runP13SameWindowNormalizedReturnBoundary input).outside_not_mem_support,
    (runP13SameWindowNormalizedReturnBoundary input).outside_adjacent⟩

/-- Cubicity owns every actual incidence at the retained return root. -/
theorem runP13SameWindowNormalizedReturnBoundary_owns_root
    (input : P13SameWindowNormalizedBoundaryInput (short := short))
    (vertex : ctx.G.Vertex)
    (adjacent : ctx.G.object.graph.Adj quiet.stub.neighbor vertex) :
    let result := runP13SameWindowNormalizedReturnBoundary input
    vertex = result.cubicStar.first ∨ vertex = result.cubicStar.second ∨
      vertex = result.cubicStar.third :=
  (runP13SameWindowNormalizedReturnBoundary input).ownsAllRootIncidences
    vertex adjacent

/-- The node-`[165]` constructor retains its strict decrease evidence. -/
theorem runP13SameWindowNormalizedReturnBoundary_rejected_strict
    (computed : P13SameWindowComputedShorterBoundary short) :
    (runP13SameWindowNormalizedReturnBoundary
      (.rejectedChord computed)).selectedReturn.path.length <
        short.setup.returnPath.path.length :=
  (runP13SameWindowNormalizedReturnBoundary
    (.rejectedChord computed)).decreaseEvidence

/-- The node-`[166]` constructor retains the original return length. -/
theorem runP13SameWindowNormalizedReturnBoundary_outside_length
    (computed : P13SameWindowComputedOutsideBoundary short) :
    (runP13SameWindowNormalizedReturnBoundary
      (.outsideBoundary computed)).selectedReturn.path.length =
        short.setup.returnPath.path.length :=
  (runP13SameWindowNormalizedReturnBoundary
    (.outsideBoundary computed)).decreaseEvidence

/-- Node `[167]` adds no primitive finite checks. -/
theorem p13SameWindowNormalizedReturnBoundary_additionalChecks_eq_zero :
    DeletedEdgeReturnNormalizedBoundary.additionalChecks = 0 :=
  DeletedEdgeReturnNormalizedBoundary.additionalChecks_eq_zero

end Erdos64EG.Internal
