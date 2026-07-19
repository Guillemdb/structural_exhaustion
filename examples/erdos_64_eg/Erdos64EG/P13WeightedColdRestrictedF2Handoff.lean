import Erdos64EG.P13WeightedColdRestrictedExactContinuation
import StructuralExhaustion.Routes.TargetDefectHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)
variable {ledger : package.PriorD6Ledger}
variable {survivor : package.LocalCorridorSurvivor ledger}

/-!
# Exact F2 target-defect handoff at node [153]

This is the existing F2 edge, not a new case.  It retains the literal earlier
and current prefix pieces and the proof-selected outside context already stored
by `StageF2`, then applies the framework target-defect route unchanged.
-/

/-- The framework source carried by one literal F2 occurrence. -/
noncomputable def StageF2.targetDefectSource
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    Routes.TargetDefectHandoff.Source packedStaticInput
      twoBoundaryEnumeration ctx where
  branch := ctx.toBranchContext
  branch_eq := rfl
  left := f2.pair.EarlierPiece
  right := f2.pair.CurrentPiece
  outside := f2.distinction.outside
  differs := f2.distinction.differs

/-- Proof-carrying execution of the original F2 outgoing edge. -/
structure StageF2RoutedHandoff {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) where
  residual : Routes.TargetDefectHandoff.Residual packedStaticInput
    twoBoundaryEnumeration ctx
  exactSource : residual.source = f2.targetDefectSource package

/-- Route the exact F2 payload without changing either prefix piece or its
selected distinguishing context. -/
noncomputable def StageF2.routeTargetDefect
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    package.StageF2RoutedHandoff f2 where
  residual := Routes.TargetDefectHandoff.handoff packedStaticInput
    twoBoundaryEnumeration ctx (f2.targetDefectSource package)
  exactSource := rfl

@[simp] theorem StageF2.routed_left
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    (f2.routeTargetDefect package).residual.source.left =
      f2.pair.EarlierPiece := by
  rw [(f2.routeTargetDefect package).exactSource]
  rfl

@[simp] theorem StageF2.routed_right
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    (f2.routeTargetDefect package).residual.source.right =
      f2.pair.CurrentPiece := by
  rw [(f2.routeTargetDefect package).exactSource]
  rfl

@[simp] theorem StageF2.routed_outside
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    (f2.routeTargetDefect package).residual.source.outside =
      f2.distinction.outside := by
  rw [(f2.routeTargetDefect package).exactSource]
  rfl

/-- The routed payload is exactly the target-defective pair asserted by F2. -/
theorem StageF2.routed_targetDefective
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    MinimumDegreeCycleReplacement.TargetDefective packedStaticInput
      twoBoundaryEnumeration
      (f2.routeTargetDefect package).residual.source.left
      (f2.routeTargetDefect package).residual.source.right :=
  (f2.routeTargetDefect package).residual.source.targetDefective

theorem StageF2.routed_ambient_preserved
    {stage : package.Stage}
    (f2 : package.StageF2 survivor stage) :
    (f2.routeTargetDefect package).residual.source.branch.G = ctx.G :=
  Routes.TargetDefectHandoff.ambient_preserved packedStaticInput
    twoBoundaryEnumeration ctx (f2.routeTargetDefect package).residual.source

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
