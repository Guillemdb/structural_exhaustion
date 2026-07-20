import Erdos64EG.Future.P13SameWindowLongPrefixStateLabels
import StructuralExhaustion.Graph.LongPrefixDegreeRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [179]: exact-degree refinement of the long-prefix collision

The full D4--D7 response family is not available from node `[164]`.  This
node therefore performs the earliest unconditional graph-owned refinement:
it consumes node `[164]`'s exact routed output, evaluates the full degrees of
its two retained literal vertices, and returns exact-degree equality or an
unequal pair with the already-proved congruence modulo four.  The identical
packing-membership bit is retained on both branches.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {long : P13SameWindowLongOutput fork quiet}
variable {source164 : P13SameWindowLongPrefixStateSource fork quiet long}

/-- Exact predecessor gate: node `[179]` cannot be run on a caller-authored
coarse collision. -/
structure P13SameWindowLongPrefixDegreeSource where
  node164 : P13SameWindowLongPrefixStateLabels source164
  node164Exact : node164 = runP13SameWindowLongPrefixStateLabels source164

noncomputable def p13SameWindowLongPrefixDegreeSource :
    P13SameWindowLongPrefixDegreeSource (source164 := source164) :=
  ⟨runP13SameWindowLongPrefixStateLabels source164, rfl⟩

namespace P13SameWindowLongPrefixDegreeSource

variable (source179 : P13SameWindowLongPrefixDegreeSource
  (source164 := source164))

noncomputable def graphSource :
    LongPrefixDegreeRefinement.Source
      (input := p13SameWindowLongPrefixObservedInput source164) :=
  ⟨source179.node164.routed.refinement⟩

theorem exact_node164 :
    source179.node164 = runP13SameWindowLongPrefixStateLabels source164 :=
  source179.node164Exact

theorem exact_ct10_refinement :
    source179.node164.routed.refinement =
      (runP13SameWindowLongPrefixStateLabels source164).routed.refinement := by
  rw [source179.node164Exact]

theorem exact_ct10_run :
    source179.node164.routed.classification =
      CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
        (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
          source179.node164.routed.source.observed) :=
  source179.node164.routed.classificationExact

theorem exact_ct10_promoted :
    source179.node164.routed.classification.terminal = .promoted := by
  rw [source179.node164Exact]
  exact runP13SameWindowLongPrefixStateLabels_ct10_terminal source164

theorem exact_ct10_promotion_responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False := by
  exact Routes.LongPrefixObservedLabel.semantic_first_missing_responseContexts
    (P := PackedProblem) ctx.toBranchContext
    source179.node164.routed.refinement

theorem exact_ct10_trace :
    source179.node164.routed.classification.trace =
      [.entry, .table, .direct, .missing, .promotion, .promotedTerminal] := by
  rw [source179.node164Exact]
  exact runP13SameWindowLongPrefixStateLabels_ct10_trace source164

end P13SameWindowLongPrefixDegreeSource

theorem p13SameWindowLongPrefixDegree_firstVertex_exact
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    source179.graphSource.firstVertex =
      p13SameWindowLongPrefixVertex source164
        (p13SameWindowLongPrefixFirstNineEmbedding source164
          source179.graphSource.first) := by
  exact p13SameWindowLongPrefixObservedVertex_exact source164 _

theorem p13SameWindowLongPrefixDegree_secondVertex_exact
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    source179.graphSource.secondVertex =
      p13SameWindowLongPrefixVertex source164
        (p13SameWindowLongPrefixFirstNineEmbedding source164
          source179.graphSource.second) := by
  exact p13SameWindowLongPrefixObservedVertex_exact source164 _

theorem p13SameWindowLongPrefixDegree_firstDegree_exact
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    source179.graphSource.firstDegree = ctx.G.object.degree
      (p13SameWindowLongPrefixVertex source164
        (p13SameWindowLongPrefixFirstNineEmbedding source164
          source179.graphSource.first)) := by
  unfold LongPrefixDegreeRefinement.Source.firstDegree
  rw [p13SameWindowLongPrefixDegree_firstVertex_exact source179]

theorem p13SameWindowLongPrefixDegree_secondDegree_exact
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    source179.graphSource.secondDegree = ctx.G.object.degree
      (p13SameWindowLongPrefixVertex source164
        (p13SameWindowLongPrefixFirstNineEmbedding source164
          source179.graphSource.second)) := by
  unfold LongPrefixDegreeRefinement.Source.secondDegree
  rw [p13SameWindowLongPrefixDegree_secondVertex_exact source179]

abbrev P13SameWindowLongPrefixDegreeResult
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :=
  LongPrefixDegreeRefinement.Result source179.graphSource

noncomputable def runP13SameWindowLongPrefixDegreeRefinement
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    P13SameWindowLongPrefixDegreeResult source179 :=
  LongPrefixDegreeRefinement.run source179.graphSource

theorem runP13SameWindowLongPrefixDegreeRefinement_exhaustive
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    (∃ residual,
      runP13SameWindowLongPrefixDegreeRefinement source179 =
        .exactDegree residual) ∨
    (∃ residual,
      runP13SameWindowLongPrefixDegreeRefinement source179 =
        .congruentDegreeGap residual) :=
  LongPrefixDegreeRefinement.run_exhaustive _

theorem runP13SameWindowLongPrefixDegreeRefinement_distinct
    (source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    source179.graphSource.first ≠ source179.graphSource.second :=
  LongPrefixDegreeRefinement.source_occurrences_distinct _

theorem runP13SameWindowLongPrefixDegreeRefinement_visibleChecks
    (_source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    LongPrefixDegreeRefinement.visibleChecks (object := ctx.G.object) ≤
      2 * (ctx.G.object.input.vertices.card + 1) :=
  LongPrefixDegreeRefinement.visibleChecks_le

/-- The dependent context is unchanged; no graph or branch state is rebuilt. -/
theorem runP13SameWindowLongPrefixDegreeRefinement_ambient_preserved
    (_source179 : P13SameWindowLongPrefixDegreeSource
      (source164 := source164)) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
