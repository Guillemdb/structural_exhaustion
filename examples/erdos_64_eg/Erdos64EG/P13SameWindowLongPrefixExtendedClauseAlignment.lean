import Erdos64EG.P13SameWindowLongPrefixLocalClauseAlignment
import StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u


/-! # Node [186]: second-block local adjacency-clause refinement -/

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

structure P13SameWindowLongPrefixExtendedClauseSource where
  node183 : P13SameWindowLongPrefixLocalClauseResult source183
  node183Exact : node183 =
    runP13SameWindowLongPrefixLocalClauseAlignment source183

noncomputable def p13SameWindowLongPrefixExtendedClauseSource :
    P13SameWindowLongPrefixExtendedClauseSource (source183 := source183) :=
  ⟨runP13SameWindowLongPrefixLocalClauseAlignment source183, rfl⟩

theorem p13SameWindowLongPrefix_firstEighteen
    (source164 : P13SameWindowLongPrefixStateSource fork quiet long) :
    18 ≤ (p13SameWindowLongCorridorSupport
      (ctx := ctx) (quiet := quiet)).length := by
  have exceeds := source164.node163.handoff.source.exceeds
  rw [p13SameWindowLongPrefixSource_scale source164,
    p13SameWindowLongPrefixSource_supportLength source164] at exceeds
  norm_num [p13ColdD1D3BaseThreshold] at exceeds ⊢
  omega

namespace P13SameWindowLongPrefixExtendedClauseSource

variable (source186 : P13SameWindowLongPrefixExtendedClauseSource
  (source183 := source183))

noncomputable def graphSource :
    LongPrefixExtendedClauseAlignment.Source
      (input := p13SameWindowLongPrefixObservedInput source164) where
  localSource := source183.graphSource
  localResult := source186.node183.classification
  localResultExact := by
    rw [source186.node183Exact]
    rfl
  firstEighteen := p13SameWindowLongPrefix_firstEighteen source164

theorem exact_node183 :
    source186.node183 =
      runP13SameWindowLongPrefixLocalClauseAlignment source183 :=
  source186.node183Exact

theorem retained_degree_result :
    source186.graphSource.localSource.degreeResult =
      LongPrefixDegreeRefinement.run
        source186.graphSource.localSource.degreeSource :=
  source186.graphSource.localSource.degreeResultExact

theorem retained_ct10_responseContexts
    (source : P13SameWindowLongPrefixExtendedClauseSource
      (source183 := source183)) :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False :=
  P13SameWindowLongPrefixLocalClauseResult.responseContexts source.node183

end P13SameWindowLongPrefixExtendedClauseSource

structure P13SameWindowLongPrefixExtendedClauseResult
    (source186 : P13SameWindowLongPrefixExtendedClauseSource
      (source183 := source183)) where
  classification : LongPrefixExtendedClauseAlignment.Result source186.graphSource
  responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False

noncomputable def runP13SameWindowLongPrefixExtendedClauseAlignment
    (source186 : P13SameWindowLongPrefixExtendedClauseSource
      (source183 := source183)) :
    P13SameWindowLongPrefixExtendedClauseResult source186 where
  classification := LongPrefixExtendedClauseAlignment.run source186.graphSource
  responseContexts :=
    P13SameWindowLongPrefixExtendedClauseSource.retained_ct10_responseContexts
      (ctx := ctx) source186

theorem runP13SameWindowLongPrefixExtendedClauseAlignment_exhaustive
    (source186 : P13SameWindowLongPrefixExtendedClauseSource
      (source183 := source183)) :
    (∃ mismatch,
      (runP13SameWindowLongPrefixExtendedClauseAlignment source186).classification =
        .inheritedMismatch mismatch) ∨
    (∃ first second,
      (runP13SameWindowLongPrefixExtendedClauseAlignment source186).classification =
        .secondMismatch first second) ∨
    (∃ first second,
      (runP13SameWindowLongPrefixExtendedClauseAlignment source186).classification =
        .firstEighteenAligned first second) := by
  simpa [runP13SameWindowLongPrefixExtendedClauseAlignment] using
    LongPrefixExtendedClauseAlignment.run_exhaustive source186.graphSource

theorem runP13SameWindowLongPrefixExtendedClauseAlignment_visibleChecks
    (_source186 : P13SameWindowLongPrefixExtendedClauseSource
      (source183 := source183)) :
    LongPrefixExtendedClauseAlignment.visibleChecks ≤
      18 * (ctx.G.object.input.vertices.card + 1) :=
  LongPrefixExtendedClauseAlignment.visibleChecks_polynomial

theorem runP13SameWindowLongPrefixExtendedClauseAlignment_ambient_preserved
    (_source186 : P13SameWindowLongPrefixExtendedClauseSource
      (source183 := source183)) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
