import Erdos64EG.Future.P13SameWindowBaseScaleSplit
import StructuralExhaustion.Routes.LongFiniteSupportHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdGermScale

universe u

/-!
# Node [163]: exact long-support prefix handoff

This module consumes an equality witnessing that node `[161]` returned its
long constructor.  It embeds the forced first `Q_base + 1` literal support
positions into that same corridor support and exposes the generic local
position classifier.

No repetition, CT17 semantics, D4--D7 reconstruction, density statement, or
ambient-universe enumeration is asserted here.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}

/-- Proof-carrying long output of the exact node-`[161]` execution. -/
structure P13SameWindowLongOutput
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork) where
  residual : LongSupportResidual
    (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
    quiet.stub quiet.germ p13ColdD1D3BaseThreshold
  runExact : runP13SameWindowBaseScaleSplit fork quiet = .long residual

/-- Generic source formed from the literal graph-owned corridor length and
the exact strict inequality retained by node `[161]`. -/
noncomputable def p13SameWindowLongSource
    {fork : P13ActualAttachmentColdFork ctx previous window}
    {quiet : P13SameWindowQuietOutput fork}
    (long : P13SameWindowLongOutput fork quiet) :
    Routes.LongFiniteSupportHandoff.Source ctx.toBranchContext where
  supportLength :=
    ((p13SelectedWindowCorridorProducer ctx).ambientReturn quiet.stub).support.length
  scale := p13ColdD1D3BaseThreshold
  exceeds := long.residual.exceeds

/-- Exact node-`[163]` result.  Its context and source remain indexed by the
computed node-`[161]` long branch. -/
structure P13SameWindowLongSupportPrefix
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) where
  handoff : Routes.LongFiniteSupportHandoff.Residual ctx.toBranchContext
  exactSource : handoff.source = p13SameWindowLongSource long

/-- Execute the forced generic handoff; no route result is supplied by the
caller. -/
noncomputable def runP13SameWindowLongSupportPrefix
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) :
    P13SameWindowLongSupportPrefix fork quiet long where
  handoff := Routes.LongFiniteSupportHandoff.handoff
    (p13SameWindowLongSource long)
  exactSource := rfl

theorem p13SameWindowLongSupportPrefix_exact_length
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) :
    (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source.supportLength =
      ((p13SelectedWindowCorridorProducer ctx).ambientReturn quiet.stub).support.length := by
  rw [(runP13SameWindowLongSupportPrefix fork quiet long).exactSource]
  rfl

theorem p13SameWindowLongSupportPrefix_exact_scale
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) :
    (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source.scale =
      p13ColdD1D3BaseThreshold := by
  rw [(runP13SameWindowLongSupportPrefix fork quiet long).exactSource]
  rfl

/-- The forced local prefix has exactly `Q_base + 1` positions. -/
theorem p13SameWindowLongSupportPrefix_card
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) :
    (Routes.LongFiniteSupportHandoff.prefixPositions
      (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source).card =
        p13ColdD1D3BaseThreshold + 1 := by
  rw [Routes.LongFiniteSupportHandoff.prefixPositions_card,
    p13SameWindowLongSupportPrefix_exact_scale fork quiet long]

/-- The unique extra prefix position maps to literal support index
`Q_base`. -/
theorem p13SameWindowLongSupportOverflowImage_val
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) :
    (Routes.LongFiniteSupportHandoff.overflowImage
      (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source).1 =
        p13ColdD1D3BaseThreshold := by
  rw [Routes.LongFiniteSupportHandoff.overflowImage_val,
    p13SameWindowLongSupportPrefix_exact_scale fork quiet long]

/-- The forced `Q_base + 1` prefix splits exhaustively into its first
`Q_base` indices and the unique overflow index. -/
theorem p13SameWindowLongSupportPrefixClass_exhaustive
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source) :
    (∃ index embeddingExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition
        (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position =
          .base index embeddingExact) ∨
    (∃ overflowExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition
        (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position =
          .overflow overflowExact) :=
  Routes.LongFiniteSupportHandoff.classifyPrefixPosition_exhaustive
    (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position

/-- The overflow classifier outcome is unique and occurs exactly at the
canonical literal index `Q_base`. -/
theorem p13SameWindowLongSupportPrefix_overflow_iff
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source) :
    (∃ overflowExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition
        (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position =
          .overflow overflowExact) ↔
      position = Routes.LongFiniteSupportHandoff.overflow
        (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source :=
  Routes.LongFiniteSupportHandoff.classifyPrefixPosition_overflow_iff
    (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position

/-- Every supplied position of the identical routed support is classified
locally as belonging to the exact prefix or lying after it. -/
theorem p13SameWindowLongSupportPositionClass_exhaustive
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet)
    (position : Routes.LongFiniteSupportHandoff.Position
      (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source) :
    (∃ index embeddingExact,
      Routes.LongFiniteSupportHandoff.classifyPosition
        (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position =
          .inPrefix index embeddingExact) ∨
    (∃ lowerBound,
      Routes.LongFiniteSupportHandoff.classifyPosition
        (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position =
          .afterPrefix lowerBound) :=
  Routes.LongFiniteSupportHandoff.classifyPosition_exhaustive
    (runP13SameWindowLongSupportPrefix fork quiet long).handoff.source position

/-- The route preserves the identical minimal-counterexample graph by its
dependent branch-context index. -/
theorem p13SameWindowLongSupportPrefix_ambient_preserved
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (_long : P13SameWindowLongOutput fork quiet) :
    ctx.toBranchContext.G = ctx.G :=
  rfl

/-- Node `[163]` performs no scan.  Constructing the prefix inclusion is
constant-time arithmetic, and classifying a supplied position uses one
comparison. -/
def p13SameWindowLongSupportPrefixChecks : Nat := 0

theorem p13SameWindowLongSupportPrefixChecks_eq_zero :
    p13SameWindowLongSupportPrefixChecks = 0 :=
  rfl

/-- Classifying one supplied prefix position costs one natural-number
comparison. -/
def p13SameWindowLongSupportPrefixClassifierChecks : Nat := 1

theorem p13SameWindowLongSupportPrefixClassifierChecks_eq_one :
    p13SameWindowLongSupportPrefixClassifierChecks = 1 :=
  rfl

end Erdos64EG.Internal
