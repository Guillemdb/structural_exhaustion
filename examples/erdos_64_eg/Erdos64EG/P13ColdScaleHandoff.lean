import Erdos64EG.P13ColdCorridorProducer
import StructuralExhaustion.Routes.LongFiniteSupportHandoff

namespace Erdos64EG.Internal.P13ColdScaleHandoff

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u uCoordinate uState

/-!
# Honest long-corridor scale handoff

The node-153 corridor producer computes a short/long split at every explicit
scale.  On the long branch this module retains the exact corridor length,
scale inequality, cold structural germ, and selected minimal-counterexample
context.  It exposes the finite corridor positions, which are the only CT17
author universe currently forced by the graph proof.

This is not a CT17 execution.  In particular the current producer proves no
finite target or offset universe, no compatibility reflection theorem, and
no graph meaning for `blockValue` or `orbitValue`.  Supplying any of those as
an unconstrained parameter would turn CT17's totality into a caller-selected
answer, so the adapter stops at the typed scale residual.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous}

noncomputable abbrev corridorLength (stub : ClassifiedColdCubicStub data) : Nat :=
  (p13ColdCorridorProducer.ambientReturn stub.toGraphStub).support.length

/-- Exact generic handoff source attached to the selected counterexample. -/
noncomputable def longSource (stub : ClassifiedColdCubicStub data)
    (scale : Nat) (exceeds : scale < corridorLength stub) :
    Routes.LongFiniteSupportHandoff.Source ctx.toBranchContext where
  supportLength := corridorLength stub
  scale := scale
  exceeds := exceeds

/-- Application residual retaining the graph-owned stub and quiet germ in
addition to the generic finite-support handoff. -/
structure LongCorridorResidual (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) where
  exceeds : scale < corridorLength stub
  handoff : Routes.LongFiniteSupportHandoff.Residual ctx.toBranchContext
  exactSource : handoff.source = longSource stub scale exceeds

/-- Forced route from the graph-produced long inequality. -/
noncomputable def routeLong (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) (exceeds : scale < corridorLength stub) :
    LongCorridorResidual stub germ scale where
  exceeds := exceeds
  handoff := Routes.LongFiniteSupportHandoff.handoff
    (longSource stub scale exceeds)
  exactSource := rfl

/-- Branch-preserving image of the graph-owned scale classifier. -/
inductive RoutedScaleDecision (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) where
  | short (bounded : corridorLength stub ≤ scale)
  | long (residual : LongCorridorResidual stub germ scale)

/-- Compute the typed handoff directly from the graph classifier.  Neither
constructor is accepted from the caller. -/
noncomputable def classify (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) : RoutedScaleDecision stub germ scale :=
  match p13ColdCorridorProducer.classifyScale PowerOfTwoLength
      stub.toGraphStub germ scale with
  | .short bounded => .short bounded
  | .long exceeds => .long (routeLong stub germ scale exceeds)

theorem classify_total (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) :
    (∃ bounded, classify stub germ scale = .short bounded) ∨
    (∃ residual, classify stub germ scale = .long residual) := by
  cases equation : classify stub germ scale with
  | short bounded => exact Or.inl ⟨bounded, rfl⟩
  | long residual => exact Or.inr ⟨residual, rfl⟩

theorem routed_exact_length (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) (residual : LongCorridorResidual stub germ scale) :
    residual.handoff.source.supportLength = corridorLength stub := by
  rw [residual.exactSource]
  rfl

theorem routed_exact_scale (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) (residual : LongCorridorResidual stub germ scale) :
    residual.handoff.source.scale = scale := by
  rw [residual.exactSource]
  rfl

theorem routed_exceeds (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) (residual : LongCorridorResidual stub germ scale) :
    residual.handoff.source.scale < residual.handoff.source.supportLength :=
  residual.handoff.source.exceeds

theorem routed_position_count (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) (residual : LongCorridorResidual stub germ scale) :
    (Routes.LongFiniteSupportHandoff.positions residual.handoff.source).card =
      corridorLength stub := by
  rw [Routes.LongFiniteSupportHandoff.positions_card,
    routed_exact_length stub germ scale residual]

/-- The context index fixes the application residual to the identical graph. -/
theorem routed_ambient_preserved (stub : ClassifiedColdCubicStub data)
    (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
      p13ColdCorridorProducer PowerOfTwoLength stub.toGraphStub)
    (scale : Nat) (_residual : LongCorridorResidual stub germ scale) :
    ctx.toBranchContext.G = ctx.G :=
  rfl

end Erdos64EG.Internal.P13ColdScaleHandoff
