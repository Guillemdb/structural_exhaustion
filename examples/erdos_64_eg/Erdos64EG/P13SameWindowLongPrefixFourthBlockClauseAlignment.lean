import Erdos64EG.P13SameWindowLongPrefixThirdBlockClauseAlignment
import StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-! # Node [192]: fourth-block local adjacency-clause refinement -/

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

structure P13SameWindowLongPrefixFourthBlockClauseSource where
  node189 : P13SameWindowLongPrefixThirdBlockClauseResult source189
  node189Exact : node189 =
    runP13SameWindowLongPrefixThirdBlockClauseAlignment source189

noncomputable def p13SameWindowLongPrefixFourthBlockClauseSource :
    P13SameWindowLongPrefixFourthBlockClauseSource (source189 := source189) :=
  ⟨runP13SameWindowLongPrefixThirdBlockClauseAlignment source189, rfl⟩

theorem p13SameWindowLongPrefix_firstThirtySix
    (source164 : P13SameWindowLongPrefixStateSource fork quiet long) :
    36 ≤ (p13SameWindowLongCorridorSupport
      (ctx := ctx) (quiet := quiet)).length := by
  have exceeds := source164.node163.handoff.source.exceeds
  rw [p13SameWindowLongPrefixSource_scale source164,
    p13SameWindowLongPrefixSource_supportLength source164] at exceeds
  norm_num [p13ColdD1D3BaseThreshold] at exceeds ⊢
  omega

namespace P13SameWindowLongPrefixFourthBlockClauseSource

variable (source192 : P13SameWindowLongPrefixFourthBlockClauseSource
  (source189 := source189))

noncomputable def graphSource :
    LongPrefixFourthBlockClauseAlignment.Source
      (input := p13SameWindowLongPrefixObservedInput source164) where
  thirdSource := source189.graphSource
  thirdResult := source192.node189.classification
  thirdResultExact := by
    rw [source192.node189Exact]
    rfl
  firstThirtySix := p13SameWindowLongPrefix_firstThirtySix source164

theorem exact_node189 :
    source192.node189 =
      runP13SameWindowLongPrefixThirdBlockClauseAlignment source189 :=
  source192.node189Exact

theorem retained_degree_result :
    source192.graphSource.thirdSource.extendedSource.localSource.degreeResult =
      LongPrefixDegreeRefinement.run
        source192.graphSource.thirdSource.extendedSource.localSource.degreeSource :=
  source192.graphSource.thirdSource.extendedSource.localSource.degreeResultExact

theorem retained_ct10_responseContexts
    (source : P13SameWindowLongPrefixFourthBlockClauseSource
      (source189 := source189)) :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False :=
  P13SameWindowLongPrefixThirdBlockClauseResult.responseContexts source.node189

end P13SameWindowLongPrefixFourthBlockClauseSource

structure P13SameWindowLongPrefixFourthBlockClauseResult
    (source192 : P13SameWindowLongPrefixFourthBlockClauseSource
      (source189 := source189)) where
  classification : LongPrefixFourthBlockClauseAlignment.Result source192.graphSource
  responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False

noncomputable def runP13SameWindowLongPrefixFourthBlockClauseAlignment
    (source192 : P13SameWindowLongPrefixFourthBlockClauseSource
      (source189 := source189)) :
    P13SameWindowLongPrefixFourthBlockClauseResult source192 where
  classification := LongPrefixFourthBlockClauseAlignment.run source192.graphSource
  responseContexts :=
    P13SameWindowLongPrefixFourthBlockClauseSource.retained_ct10_responseContexts
      (ctx := ctx) source192

theorem runP13SameWindowLongPrefixFourthBlockClauseAlignment_exhaustive
    (source192 : P13SameWindowLongPrefixFourthBlockClauseSource
      (source189 := source189)) :
    (∃ mismatch,
      (runP13SameWindowLongPrefixFourthBlockClauseAlignment source192).classification =
        .inheritedFirstMismatch mismatch) ∨
    (∃ first second,
      (runP13SameWindowLongPrefixFourthBlockClauseAlignment source192).classification =
        .inheritedSecondMismatch first second) ∨
    (∃ first second third,
      (runP13SameWindowLongPrefixFourthBlockClauseAlignment source192).classification =
        .inheritedThirdMismatch first second third) ∨
    (∃ first second third fourth,
      (runP13SameWindowLongPrefixFourthBlockClauseAlignment source192).classification =
        .fourthMismatch first second third fourth) ∨
    (∃ first second third fourth,
      (runP13SameWindowLongPrefixFourthBlockClauseAlignment source192).classification =
        .firstThirtySixAligned first second third fourth) := by
  simpa [runP13SameWindowLongPrefixFourthBlockClauseAlignment] using
    LongPrefixFourthBlockClauseAlignment.run_exhaustive source192.graphSource

theorem runP13SameWindowLongPrefixFourthBlockClauseAlignment_visibleChecks
    (_source192 : P13SameWindowLongPrefixFourthBlockClauseSource
      (source189 := source189)) :
    LongPrefixFourthBlockClauseAlignment.visibleChecks ≤
      18 * (ctx.G.object.input.vertices.card + 1) :=
  LongPrefixFourthBlockClauseAlignment.visibleChecks_polynomial

theorem runP13SameWindowLongPrefixFourthBlockClauseAlignment_ambient_preserved
    (_source192 : P13SameWindowLongPrefixFourthBlockClauseSource
      (source189 := source189)) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
