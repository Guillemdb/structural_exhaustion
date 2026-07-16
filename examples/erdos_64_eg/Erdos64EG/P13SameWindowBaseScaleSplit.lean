import Erdos64EG.P13SameWindowStructuralFrontier
import StructuralExhaustion.Core.FixedTwoBoundaryCutState
import StructuralExhaustion.Graph.InducedPathColdGermScale

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdGermScale

universe u

/-!
# Node [161]: honest D1--D3 base-scale split

This module consumes only an equality witnessing that node `[159]` actually
returned its quiet constructor.  It compares the retained corridor support
with the exact D1--D3 state-cardinality threshold
`4^2 * 13^2 * 2^13`.  The result has exactly a short and a long constructor.

There is no D4--D7 coordinate, repetition conclusion, bounded-germ semantic
promotion, CT3 execution, or density statement here.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}

private noncomputable abbrev P13CorridorProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  InducedPathColdCorridor.firstFailureProfile
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable

/-- The exact normalized-state cardinal available before any D4--D7 local
coordinate is supplied. -/
abbrev p13ColdD1D3BaseThreshold : Nat :=
  4 ^ 2 * 13 ^ 2 * 2 ^ 13

/-- The base threshold is precisely the fixed two-boundary state cardinal
with an empty D4--D7 coordinate alphabet.  This theorem makes no claim that
the empty alphabet is complete for D4--D7. -/
theorem p13ColdD1D3BaseThreshold_eq_stateCard :
    p13ColdD1D3BaseThreshold =
      Fintype.card
        (Core.FixedTwoBoundaryCutState.State (Fin 0)) := by
  rw [Core.FixedTwoBoundaryCutState.state_card]
  norm_num [p13ColdD1D3BaseThreshold]

/-- Proof-carrying input for node `[161]`.  The equality prevents a caller
from supplying an arbitrary structural germ that was not the computed quiet
output of the exact node-`[159]` run. -/
structure P13SameWindowQuietOutput
    (fork : P13ActualAttachmentColdFork ctx previous window) where
  stub : InducedPathColdCorridor.CubicStub ctx.G.object
  sameWindow : stub.window = selectedConnectorWindowIndex window
  noEvent : ∀ stage, stage ∈ ((P13CorridorProfile ctx).stages stub).values →
    ¬(P13CorridorProfile ctx).Event stub stage
  germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
    (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub
  runExact : runP13SameWindowStructuralFrontier fork =
    .quiet stub sameWindow noEvent germ

/-- Exact two-way base-scale result.  All node-`[159]` quiet provenance is
retained in the indexed input. -/
inductive P13SameWindowBaseScaleSplit
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork) where
  | short (residual : BoundedSameInterfaceResidual
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      quiet.stub quiet.germ p13ColdD1D3BaseThreshold)
  | long (residual : LongSupportResidual
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      quiet.stub quiet.germ p13ColdD1D3BaseThreshold)

/-- Execute one graph-owned natural-number comparison at the fixed D1--D3
threshold. -/
noncomputable def runP13SameWindowBaseScaleSplit
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork) :
    P13SameWindowBaseScaleSplit fork quiet :=
  match InducedPathColdGermScale.route
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      quiet.stub quiet.germ p13ColdD1D3BaseThreshold with
  | .short residual => .short residual
  | .long residual => .long residual

/-- The computed split has no third outcome. -/
theorem runP13SameWindowBaseScaleSplit_exhaustive
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork) :
    (∃ residual, runP13SameWindowBaseScaleSplit fork quiet = .short residual) ∨
    (∃ residual, runP13SameWindowBaseScaleSplit fork quiet = .long residual) := by
  cases equation : runP13SameWindowBaseScaleSplit fork quiet with
  | short residual => exact Or.inl ⟨residual, rfl⟩
  | long residual => exact Or.inr ⟨residual, rfl⟩

/-- The visible execution cost of node `[161]` is one support-length
comparison; construction of the proof-carrying corridor belongs to node
`[159]`. -/
def p13SameWindowBaseScaleComparisonCount : Nat := 1

theorem p13SameWindowBaseScaleComparisonCount_eq_one :
    p13SameWindowBaseScaleComparisonCount = 1 := rfl

end Erdos64EG.Internal
