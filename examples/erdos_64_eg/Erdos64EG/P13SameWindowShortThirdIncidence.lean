import Erdos64EG.P13SameWindowBaseScaleSplit
import StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdGermScale

universe u

/-!
# Node [162]: the third incidence at one short return root

This module consumes an equality proving that the exact node-`[161]` run took
its short branch.  It applies the graph-owned deleted-return classifier only
at the root of that supplied return.  The two results say exactly that the
declared-order third neighbour is on the return support or outside it.

There is no semantic promotion, CT3 execution, D4--D7 coordinate, target
response, density conclusion, or scan over all support vertices here.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}

private noncomputable abbrev P13Producer
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  p13SelectedWindowCorridorProducer ctx

/-- Proof-carrying short input from the exact computed node-`[161]` split. -/
structure P13SameWindowComputedShort
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork) where
  residual : BoundedSameInterfaceResidual
    (P13Producer ctx) PowerOfTwoLength quiet.stub quiet.germ
    p13ColdD1D3BaseThreshold
  runExact : runP13SameWindowBaseScaleSplit fork quiet = .short residual

namespace P13SameWindowComputedShort

variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}

theorem root_degree_ge_three (_short : P13SameWindowComputedShort fork quiet) :
    3 ≤ ctx.G.object.degree quiet.stub.neighbor :=
  ctx.baseline.trans (ctx.G.object.minDegree_le_degree quiet.stub.neighbor)

theorem root_mem_corridor
    (_short : P13SameWindowComputedShort fork quiet) :
    quiet.stub.neighbor ∈
      ((P13Producer ctx).ambientReturn quiet.stub).support :=
  ((P13Producer ctx).ambientReturn quiet.stub).start_mem_support

theorem root_not_high (short : P13SameWindowComputedShort fork quiet) :
    ¬3 < ctx.G.object.degree quiet.stub.neighbor := by
  exact quiet.germ.allSubcubic quiet.stub.neighbor short.root_mem_corridor

/-- Thin concrete instantiation of the graph-owned root classifier. -/
noncomputable def setup (short : P13SameWindowComputedShort fork quiet) :
    DeletedEdgeReturnThirdIncidence.Setup ctx.G.object quiet.stub.dart where
  returnPath := (P13Producer ctx).returnPath quiet.stub
  degree_ge_three := short.root_degree_ge_three
  root_not_high := short.root_not_high

theorem return_support_bounded (short : P13SameWindowComputedShort fork quiet) :
    short.setup.returnPath.path.support.length ≤
      p13ColdD1D3BaseThreshold := by
  have bounded := short.residual.bounded
  change ((P13Producer ctx).returnPath quiet.stub).path.support.length ≤
    p13ColdD1D3BaseThreshold
  change (((P13Producer ctx).returnPath quiet.stub).path.mapLe
    (ctx.G.object.graph.deleteEdges_le {quiet.stub.dart.edge})).support.length ≤
      p13ColdD1D3BaseThreshold at bounded
  rw [SimpleGraph.Walk.length_support] at bounded ⊢
  change (((P13Producer ctx).returnPath quiet.stub).path.map _).length + 1 ≤
    p13ColdD1D3BaseThreshold at bounded
  rw [SimpleGraph.Walk.length_map] at bounded
  exact bounded

end P13SameWindowComputedShort

variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}

/-- Exact two-way node-`[162]` result. -/
abbrev P13SameWindowShortThirdIncidence
    (short : P13SameWindowComputedShort fork quiet) :=
  DeletedEdgeReturnThirdIncidence.Result short.setup

/-- Execute the reusable classifier on the precise short residual selected by
node `[161]`. -/
noncomputable def runP13SameWindowShortThirdIncidence
    (short : P13SameWindowComputedShort fork quiet) :
    P13SameWindowShortThirdIncidence short :=
  DeletedEdgeReturnThirdIncidence.run short.setup

theorem runP13SameWindowShortThirdIncidence_exhaustive
    (short : P13SameWindowComputedShort fork quiet) :
    (∃ member, runP13SameWindowShortThirdIncidence short =
      .nonRootChord member) ∨
    (∃ outside, runP13SameWindowShortThirdIncidence short =
      .outsideBoundary outside) :=
  DeletedEdgeReturnThirdIncidence.run_exhaustive short.setup

/-- The conservative node-local budget.  It scans the declared neighbours at
one root and tests one selected endpoint against the supplied short support. -/
theorem p13SameWindowShortThirdIncidence_visibleChecks_le
    (short : P13SameWindowComputedShort fork quiet) :
    DeletedEdgeReturnThirdIncidence.visibleChecks short.setup ≤
      2 * ctx.G.object.input.vertices.card + 3 +
        p13ColdD1D3BaseThreshold :=
  DeletedEdgeReturnThirdIncidence.visibleChecks_le short.setup
    short.return_support_bounded

end Erdos64EG.Internal
