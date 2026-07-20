import Erdos64EG.Future.P13SameWindowShortThirdIncidence
import StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [166]: the selected outside incidence as a cubic boundary star

This is a thin indexing layer over
`Graph.DeletedEdgeReturnBoundaryStar`.  Its sole input is an equality proving
that the exact node-`[162]` runner returned `.outsideBoundary`.  It retains the
same short residual, selected window, return, and selected third incidence.

There is no additional scan and no claim about
`InducedPathColdSkeleton.BoundaryStub`, outside-vertex collections,
components, successors, D4--D7, CT3, or density.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}

/-- Exact computed node-`[162]` outside branch. -/
structure P13SameWindowComputedOutsideBoundary
    (short : P13SameWindowComputedShort fork quiet) where
  outside : short.setup.third.hit.value ∉
    short.setup.returnPath.path.support
  runExact : runP13SameWindowShortThirdIncidence short =
    .outsideBoundary outside

namespace P13SameWindowComputedOutsideBoundary

variable {short : P13SameWindowComputedShort fork quiet}

/-- Direct handoff to the reusable graph-owned branch. -/
noncomputable def graphBranch
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    DeletedEdgeReturnBoundaryStar.OutsideRun short.setup where
  outside := outsideBranch.outside
  runExact := outsideBranch.runExact

/-- The one oriented incidence crossing from the literal return support to
the selected third endpoint. -/
noncomputable def orientedBoundary
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :=
  outsideBranch.graphBranch.orientedBoundary

theorem root_mem_return_support
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    quiet.stub.neighbor ∈ short.setup.returnPath.path.support :=
  outsideBranch.orientedBoundary.root_mem_support

theorem selected_outside_return_support
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    short.setup.third.hit.value ∉ short.setup.returnPath.path.support :=
  outsideBranch.orientedBoundary.selected_not_mem_support

theorem selected_adjacent_root
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    ctx.G.object.graph.Adj quiet.stub.neighbor
      short.setup.third.hit.value :=
  outsideBranch.orientedBoundary.selected_adjacent

theorem selected_ne_first_return
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    short.setup.third.hit.value ≠ short.setup.firstNext :=
  outsideBranch.orientedBoundary.selected_ne_first_return

theorem selected_ne_restored_endpoint
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    short.setup.third.hit.value ≠ quiet.stub.dart.fst :=
  outsideBranch.orientedBoundary.selected_ne_restored_endpoint

/-- Exact cubic star at the supplied return root. -/
noncomputable def cubicStar
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    CubicStar.Data ctx.G.object quiet.stub.neighbor :=
  outsideBranch.graphBranch.cubicStar

/-- The star's finite boundary ownership shape. -/
noncomputable def switchBoundaryShape
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    outsideBranch.cubicStar.SwitchBoundaryShape :=
  outsideBranch.graphBranch.switchBoundaryShape

theorem ownsAllRootIncidences
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    ∀ vertex, ctx.G.object.graph.Adj quiet.stub.neighbor vertex →
      ∃ index,
        outsideBranch.switchBoundaryShape.boundaryVertex index = vertex :=
  outsideBranch.graphBranch.ownsAllRootIncidences

/-- Node `[166]` performs no primitive checks after node `[162]`. -/
theorem additionalChecks_eq_zero
    (outsideBranch : P13SameWindowComputedOutsideBoundary short) :
    outsideBranch.graphBranch.additionalChecks = 0 :=
  outsideBranch.graphBranch.additionalChecks_eq_zero

end P13SameWindowComputedOutsideBoundary

end Erdos64EG.Internal
