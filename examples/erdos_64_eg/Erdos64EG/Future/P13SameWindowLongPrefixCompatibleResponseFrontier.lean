import Erdos64EG.Future.P13SameWindowLongPrefixFourthBlockClauseAlignment
import StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier
import StructuralExhaustion.Graph.LongPrefixCT8Response

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [195]: honest compatible-response frontier

Node 195 consumes node 192 exactly and preserves all four local-mismatch
leaves and the first-thirty-six-aligned leaf.  Its immediate local consumer
turns each mismatch into a distinguishing adjacency response on the same
fixed schedule.  Agreement on that schedule is not reinterpreted as complete
D4--D7 response equivalence: the aligned branch retains the missing semantic
and certified-reduction inputs at the manuscript boundary.
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

/-- First genuine semantic consumer after node [195].  Each of the four
fixed-block mismatch leaves becomes an actual distinguishing adjacency
response on the same corridor.  The aligned leaf retains its four proofs and
stops at the exact D4--D7-semantics and certified-reduction requirements. -/
noncomputable def resolveP13SameWindowLongPrefixCompatibleResponseFrontier
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    LongPrefixCT8Response.Resolution source195.graphSource :=
  LongPrefixCT8Response.resolve source195.graphSource
    (runP13SameWindowLongPrefixCompatibleResponseFrontier source195).frontier

theorem resolveP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive
    (source195 : P13SameWindowLongPrefixCompatibleResponseFrontierSource
      (source192 := source192)) :
    (∃ separator,
      resolveP13SameWindowLongPrefixCompatibleResponseFrontier source195 =
        .distinguishing separator) ∨
    (∃ requirement,
      resolveP13SameWindowLongPrefixCompatibleResponseFrontier source195 =
        .aligned requirement) := by
  cases equation :
      resolveP13SameWindowLongPrefixCompatibleResponseFrontier source195 with
  | distinguishing separator => exact Or.inl ⟨separator, rfl⟩
  | aligned requirement => exact Or.inr ⟨requirement, rfl⟩

/-- The post-node-[195] resolver inspects only the retained constructor.
Mismatch response inequalities are proof transport from prior scans, and the
aligned branch merely records requirements. -/
def p13SameWindowLongPrefixResponseVisibleChecks : Nat :=
  LongPrefixCompatibleResponseFrontier.visibleChecks

theorem p13SameWindowLongPrefixResponseVisibleChecks_eq :
    p13SameWindowLongPrefixResponseVisibleChecks = 1 := rfl

theorem p13SameWindowLongPrefixResponseVisibleChecks_polynomial :
    p13SameWindowLongPrefixResponseVisibleChecks ≤
      ctx.G.object.input.vertices.card + 1 := by
  unfold p13SameWindowLongPrefixResponseVisibleChecks
    LongPrefixCompatibleResponseFrontier.visibleChecks
  omega

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
