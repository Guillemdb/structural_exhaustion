import Erdos64EG.P13SameWindowLongPrefixCompatibleResponseFrontier
import StructuralExhaustion.Graph.LongPrefixAlignedDegreeGate

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Aligned long-prefix degree gate after node [195]

This is an unnumbered local connector.  It consumes the actual node-[195]
resolver output.  Mismatch separators pass through.  On the aligned leaf it
inspects the exact retained node-[179] degree constructor: a degree gap leaves
CT8, while exact degree supplies equality of the full exact type and the
explicit repeated pair.  It constructs neither D4--D7 semantics nor removal.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {long : P13SameWindowLongOutput fork quiet}
variable {source164 : P13SameWindowLongPrefixStateSource fork quiet long}
variable {source179 : P13SameWindowLongPrefixDegreeSource
  (source164 := source164)}
variable {source183 : P13SameWindowLongPrefixLocalClauseSource
  (source179 := source179)}
variable {source186 : P13SameWindowLongPrefixExtendedClauseSource
  (source183 := source183)}
variable {source189 : P13SameWindowLongPrefixThirdBlockClauseSource
  (source186 := source186)}
variable {source192 : P13SameWindowLongPrefixFourthBlockClauseSource
  (source189 := source189)}

inductive P13SameWindowLongPrefixAlignedDegreeGateResult
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) where
  | distinguishing
      (separator : LongPrefixCT8Response.DistinguishingResponse
        source195.graphSource)
  | degreeGap
      (requirement : LongPrefixCT8Response.AlignedCT8Requirement
        source195.graphSource)
      (residual : LongPrefixAlignedDegreeGate.DegreeGap
        source195.graphSource requirement)
  | exactPair
      (requirement : LongPrefixCT8Response.AlignedCT8Requirement
        source195.graphSource)
      (residual : LongPrefixAlignedDegreeGate.ExactPair.{u, u + 1, 0}
        PackedProblem source195.graphSource requirement)

noncomputable def runP13SameWindowLongPrefixAlignedDegreeGate
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    P13SameWindowLongPrefixAlignedDegreeGateResult source195 :=
  match resolveP13SameWindowLongPrefixCompatibleResponseFrontier source195 with
  | .distinguishing separator => .distinguishing separator
  | .aligned requirement =>
      match LongPrefixAlignedDegreeGate.run PackedProblem source195.graphSource
          requirement with
      | .degreeGap residual => .degreeGap requirement residual
      | .exactPair residual => .exactPair requirement residual

theorem runP13SameWindowLongPrefixAlignedDegreeGate_exhaustive
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    (∃ separator,
      runP13SameWindowLongPrefixAlignedDegreeGate source195 =
        .distinguishing separator) ∨
    (∃ requirement residual,
      runP13SameWindowLongPrefixAlignedDegreeGate source195 =
        .degreeGap requirement residual) ∨
    (∃ requirement residual,
      runP13SameWindowLongPrefixAlignedDegreeGate source195 =
        .exactPair requirement residual) := by
  cases equation : runP13SameWindowLongPrefixAlignedDegreeGate source195 with
  | distinguishing separator => exact Or.inl ⟨separator, rfl⟩
  | degreeGap requirement residual =>
      exact Or.inr (Or.inl ⟨requirement, residual, rfl⟩)
  | exactPair requirement residual =>
      exact Or.inr (Or.inr ⟨requirement, residual, rfl⟩)

theorem runP13SameWindowLongPrefixAlignedDegreeGate_visibleChecks :
    LongPrefixAlignedDegreeGate.visibleChecks ≤
      ctx.G.object.input.vertices.card + 1 :=
  LongPrefixAlignedDegreeGate.visibleChecks_polynomial

end Erdos64EG.Internal
