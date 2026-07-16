import Erdos64EG.P13SameWindowLongPrefixExtendedClauseAlignment
import StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-! # Node [189]: third-block local adjacency-clause refinement -/

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

structure P13SameWindowLongPrefixThirdBlockClauseSource where
  node186 : P13SameWindowLongPrefixExtendedClauseResult source186
  node186Exact : node186 =
    runP13SameWindowLongPrefixExtendedClauseAlignment source186

noncomputable def p13SameWindowLongPrefixThirdBlockClauseSource :
    P13SameWindowLongPrefixThirdBlockClauseSource (source186 := source186) :=
  ⟨runP13SameWindowLongPrefixExtendedClauseAlignment source186, rfl⟩

theorem p13SameWindowLongPrefix_firstTwentySeven
    (source164 : P13SameWindowLongPrefixStateSource fork quiet long) :
    27 ≤ (p13SameWindowLongCorridorSupport
      (ctx := ctx) (quiet := quiet)).length := by
  have exceeds := source164.node163.handoff.source.exceeds
  rw [p13SameWindowLongPrefixSource_scale source164,
    p13SameWindowLongPrefixSource_supportLength source164] at exceeds
  norm_num [p13ColdD1D3BaseThreshold] at exceeds ⊢
  omega

namespace P13SameWindowLongPrefixThirdBlockClauseSource

variable (source189 : P13SameWindowLongPrefixThirdBlockClauseSource
  (source186 := source186))

noncomputable def graphSource :
    LongPrefixThirdBlockClauseAlignment.Source
      (input := p13SameWindowLongPrefixObservedInput source164) where
  extendedSource := source186.graphSource
  extendedResult := source189.node186.classification
  extendedResultExact := by
    rw [source189.node186Exact]
    rfl
  firstTwentySeven := p13SameWindowLongPrefix_firstTwentySeven source164

theorem exact_node186 :
    source189.node186 =
      runP13SameWindowLongPrefixExtendedClauseAlignment source186 :=
  source189.node186Exact

theorem retained_degree_result :
    source189.graphSource.extendedSource.localSource.degreeResult =
      LongPrefixDegreeRefinement.run
        source189.graphSource.extendedSource.localSource.degreeSource :=
  source189.graphSource.extendedSource.localSource.degreeResultExact

theorem retained_ct10_responseContexts
    (source : P13SameWindowLongPrefixThirdBlockClauseSource
      (source186 := source186)) :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False :=
  P13SameWindowLongPrefixExtendedClauseResult.responseContexts source.node186

end P13SameWindowLongPrefixThirdBlockClauseSource

structure P13SameWindowLongPrefixThirdBlockClauseResult
    (source189 : P13SameWindowLongPrefixThirdBlockClauseSource
      (source186 := source186)) where
  classification : LongPrefixThirdBlockClauseAlignment.Result source189.graphSource
  responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False

noncomputable def runP13SameWindowLongPrefixThirdBlockClauseAlignment
    (source189 : P13SameWindowLongPrefixThirdBlockClauseSource
      (source186 := source186)) :
    P13SameWindowLongPrefixThirdBlockClauseResult source189 where
  classification := LongPrefixThirdBlockClauseAlignment.run source189.graphSource
  responseContexts :=
    P13SameWindowLongPrefixThirdBlockClauseSource.retained_ct10_responseContexts
      (ctx := ctx) source189

theorem runP13SameWindowLongPrefixThirdBlockClauseAlignment_exhaustive
    (source189 : P13SameWindowLongPrefixThirdBlockClauseSource
      (source186 := source186)) :
    (∃ mismatch,
      (runP13SameWindowLongPrefixThirdBlockClauseAlignment source189).classification =
        .inheritedFirstMismatch mismatch) ∨
    (∃ first second,
      (runP13SameWindowLongPrefixThirdBlockClauseAlignment source189).classification =
        .inheritedSecondMismatch first second) ∨
    (∃ first second third,
      (runP13SameWindowLongPrefixThirdBlockClauseAlignment source189).classification =
        .thirdMismatch first second third) ∨
    (∃ first second third,
      (runP13SameWindowLongPrefixThirdBlockClauseAlignment source189).classification =
        .firstTwentySevenAligned first second third) := by
  simpa [runP13SameWindowLongPrefixThirdBlockClauseAlignment] using
    LongPrefixThirdBlockClauseAlignment.run_exhaustive source189.graphSource

theorem runP13SameWindowLongPrefixThirdBlockClauseAlignment_visibleChecks
    (_source189 : P13SameWindowLongPrefixThirdBlockClauseSource
      (source186 := source186)) :
    LongPrefixThirdBlockClauseAlignment.visibleChecks ≤
      18 * (ctx.G.object.input.vertices.card + 1) :=
  LongPrefixThirdBlockClauseAlignment.visibleChecks_polynomial

theorem runP13SameWindowLongPrefixThirdBlockClauseAlignment_ambient_preserved
    (_source189 : P13SameWindowLongPrefixThirdBlockClauseSource
      (source186 := source186)) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
