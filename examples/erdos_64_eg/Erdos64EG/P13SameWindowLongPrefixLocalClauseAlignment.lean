import Erdos64EG.P13SameWindowLongPrefixDegreeRefinement
import StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [183]: first-nine local adjacency-clause alignment

This node consumes the exact node-179 degree result and the CT10
`responseContexts` obligation retained through its node-164 source.  It scans
only adjacency from the two retained vertices to the same first nine literal
prefix occurrences.  A mismatch is returned with its exact first coordinate;
otherwise alignment is certified only on that declared nine-coordinate
schedule.  Neither branch is promoted to D4--D7 response equivalence or CT8.
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

/-- Exact predecessor gate for node `[183]`. -/
structure P13SameWindowLongPrefixLocalClauseSource where
  node179 : P13SameWindowLongPrefixDegreeResult source179
  node179Exact : node179 =
    runP13SameWindowLongPrefixDegreeRefinement source179

noncomputable def p13SameWindowLongPrefixLocalClauseSource :
    P13SameWindowLongPrefixLocalClauseSource (source179 := source179) :=
  ⟨runP13SameWindowLongPrefixDegreeRefinement source179, rfl⟩

namespace P13SameWindowLongPrefixLocalClauseSource

variable (source183 : P13SameWindowLongPrefixLocalClauseSource
  (source179 := source179))

noncomputable def graphSource :
    LongPrefixLocalClauseAlignment.Source
      (input := p13SameWindowLongPrefixObservedInput source164) where
  degreeSource := source179.graphSource
  degreeResult := source183.node179
  degreeResultExact := source183.node179Exact

theorem exact_node179 :
    source183.node179 =
      runP13SameWindowLongPrefixDegreeRefinement source179 :=
  source183.node179Exact

theorem retained_ct10_responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False :=
  source179.exact_ct10_promotion_responseContexts

end P13SameWindowLongPrefixLocalClauseSource

structure P13SameWindowLongPrefixLocalClauseResult
    (source183 : P13SameWindowLongPrefixLocalClauseSource
      (source179 := source179)) where
  classification : LongPrefixLocalClauseAlignment.Result source183.graphSource
  responseContexts :
    match (CT10.run (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        source179.node164.routed.refinement)).outcome with
    | .promoted residual =>
        residual.promotion =
          Routes.LongPrefixObservedLabel.SemanticClass.responseContexts
    | _ => False

noncomputable def runP13SameWindowLongPrefixLocalClauseAlignment
    (source183 : P13SameWindowLongPrefixLocalClauseSource
      (source179 := source179)) :
    P13SameWindowLongPrefixLocalClauseResult source183 where
  classification := LongPrefixLocalClauseAlignment.run source183.graphSource
  responseContexts :=
    P13SameWindowLongPrefixLocalClauseSource.retained_ct10_responseContexts
      (ctx := ctx) (source179 := source179)

theorem runP13SameWindowLongPrefixLocalClauseAlignment_exhaustive
    (source183 : P13SameWindowLongPrefixLocalClauseSource
      (source179 := source179)) :
    (∃ residual,
      (runP13SameWindowLongPrefixLocalClauseAlignment source183).classification =
        .firstMismatch residual) ∨
    (∃ residual,
      (runP13SameWindowLongPrefixLocalClauseAlignment source183).classification =
        .aligned residual) :=
  by
    simpa [runP13SameWindowLongPrefixLocalClauseAlignment] using
      (LongPrefixLocalClauseAlignment.run_exhaustive source183.graphSource)

theorem runP13SameWindowLongPrefixLocalClauseAlignment_visibleChecks
    (_source183 : P13SameWindowLongPrefixLocalClauseSource
      (source179 := source179)) :
    LongPrefixLocalClauseAlignment.visibleChecks ≤
      18 * (ctx.G.object.input.vertices.card + 1) :=
  LongPrefixLocalClauseAlignment.visibleChecks_polynomial

theorem runP13SameWindowLongPrefixLocalClauseAlignment_ambient_preserved
    (_source183 : P13SameWindowLongPrefixLocalClauseSource
      (source179 := source179)) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
