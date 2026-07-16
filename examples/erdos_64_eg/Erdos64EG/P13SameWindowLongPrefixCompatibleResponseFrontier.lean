import Erdos64EG.P13SameWindowLongPrefixFourthBlockClauseAlignment
import StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [195]: honest compatible-response frontier

Node 195 consumes node 192 exactly.  It preserves all four local-mismatch
leaves and the first-thirty-six-aligned leaf, but does not reinterpret a local
adjacency mismatch as a distinguishing response context or agreement on the
fixed schedule as compatible-response equivalence.  The missing graph-owned
semantic and CT8 inputs are exposed as a terminal residual interface at the
manuscript boundary.
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

structure P13SameWindowLongPrefixCompatibleResponseFrontierSource where
  node192 : P13SameWindowLongPrefixFourthBlockClauseResult source192
  node192Exact : node192 =
    runP13SameWindowLongPrefixFourthBlockClauseAlignment source192

noncomputable def p13SameWindowLongPrefixCompatibleResponseFrontierSource :
    P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192) :=
  ⟨runP13SameWindowLongPrefixFourthBlockClauseAlignment source192, rfl⟩

namespace P13SameWindowLongPrefixCompatibleResponseFrontierSource

variable (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
  (source192 := source192))

noncomputable def graphSource :
    LongPrefixCompatibleResponseFrontier.Source
      (input := p13SameWindowLongPrefixObservedInput source164) where
  fourthSource := source192.graphSource
  fourthResult := source195.node192.classification
  fourthResultExact := by
    rw [source195.node192Exact]
    rfl

theorem exact_node192 :
    source195.node192 =
      runP13SameWindowLongPrefixFourthBlockClauseAlignment source192 :=
  source195.node192Exact

theorem retained_degree_result :
    source195.graphSource.fourthSource.thirdSource.extendedSource.localSource.degreeResult =
      LongPrefixDegreeRefinement.run
        source195.graphSource.fourthSource.thirdSource.extendedSource.localSource.degreeSource :=
  source195.graphSource.fourthSource.thirdSource.extendedSource.localSource.degreeResultExact

theorem retained_ct10_responseContexts
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False :=
  P13SameWindowLongPrefixFourthBlockClauseResult.responseContexts source195.node192

end P13SameWindowLongPrefixCompatibleResponseFrontierSource

structure P13SameWindowLongPrefixCompatibleResponseFrontierResult
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) where
  frontier : LongPrefixCompatibleResponseFrontier.Result source195.graphSource
  responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False

noncomputable def runP13SameWindowLongPrefixCompatibleResponseFrontier
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    P13SameWindowLongPrefixCompatibleResponseFrontierResult source195 where
  frontier := LongPrefixCompatibleResponseFrontier.run source195.graphSource
  responseContexts :=
    P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_ct10_responseContexts
      source195

theorem runP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    (∃ mismatch obligation,
      (runP13SameWindowLongPrefixCompatibleResponseFrontier source195).frontier =
        .inheritedFirstMismatch mismatch obligation) ∨
    (∃ first second obligation,
      (runP13SameWindowLongPrefixCompatibleResponseFrontier source195).frontier =
        .inheritedSecondMismatch first second obligation) ∨
    (∃ first second third obligation,
      (runP13SameWindowLongPrefixCompatibleResponseFrontier source195).frontier =
        .inheritedThirdMismatch first second third obligation) ∨
    (∃ first second third fourth obligation,
      (runP13SameWindowLongPrefixCompatibleResponseFrontier source195).frontier =
        .fourthMismatch first second third fourth obligation) ∨
    (∃ first second third fourth obligation,
      (runP13SameWindowLongPrefixCompatibleResponseFrontier source195).frontier =
        .firstThirtySixAligned first second third fourth obligation) := by
  simpa [runP13SameWindowLongPrefixCompatibleResponseFrontier] using
    LongPrefixCompatibleResponseFrontier.run_exhaustive source195.graphSource

theorem runP13SameWindowLongPrefixCompatibleResponseFrontier_retains_node192
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    (runP13SameWindowLongPrefixCompatibleResponseFrontier
      source195).frontier.predecessor = source195.node192.classification :=
  LongPrefixCompatibleResponseFrontier.run_predecessor source195.graphSource

theorem runP13SameWindowLongPrefixCompatibleResponseFrontier_requiredInputs
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    LongPrefixCompatibleResponseFrontier.requiredInputs source195.graphSource ≤ 3 :=
  LongPrefixCompatibleResponseFrontier.requiredInputs_le_three _

theorem runP13SameWindowLongPrefixCompatibleResponseFrontier_visibleChecks
    (_source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    LongPrefixCompatibleResponseFrontier.visibleChecks ≤ 1 :=
  LongPrefixCompatibleResponseFrontier.visibleChecks_constant

theorem runP13SameWindowLongPrefixCompatibleResponseFrontier_ambient_preserved
    (_source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
