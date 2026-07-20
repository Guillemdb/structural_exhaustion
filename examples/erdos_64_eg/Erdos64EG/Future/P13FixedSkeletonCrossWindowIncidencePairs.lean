import Erdos64EG.Future.P13FixedSkeletonComponentEntries
import StructuralExhaustion.Routes.InducedPathCrossWindowIncidencePair

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Exact direct-incidence consumer for the cross-window branch

Each cross-window residual in the complete thirteen-per-cubic-window source
schedule is converted to the two opposite selected-window tokens of its
literal edge.  Component entries pass through with all boundary and schedule
data unchanged.  This stage performs no owner-change path scan and does not
enter the component D1--D4 branch.
-/

inductive P13BranchExcessCrossWindowPairRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessComponentEntry ctx) : Type (u + 1) where
  | component
      (boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object)
      (boundaryTokenExact : boundary.token = entry.source.2.stub.token)
      (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
      (inputAnchorExact : input.anchor = boundary)
  | paired
      (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
        entry.source.2.stub)
      (pair :
        Routes.InducedPathCrossWindowIncidencePair.CrossWindowIncidencePair
          entry.source.2.stub residual)
      (pairExact : pair =
        Routes.InducedPathCrossWindowIncidencePair.route
          entry.source.2.stub residual)

noncomputable def routeP13BranchExcessCrossWindowPair
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessComponentEntry ctx) :
    P13BranchExcessCrossWindowPairRoute entry := by
  cases entry.route with
  | component boundary boundaryTokenExact input inputAnchorExact =>
      exact .component boundary boundaryTokenExact input inputAnchorExact
  | crossWindow residual =>
      exact .paired residual
        (Routes.InducedPathCrossWindowIncidencePair.route
          entry.source.2.stub residual) rfl

structure P13BranchExcessCrossWindowPairEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  previous : P13BranchExcessComponentEntry ctx
  route : P13BranchExcessCrossWindowPairRoute previous
  routeExact : route = routeP13BranchExcessCrossWindowPair previous

noncomputable def p13BranchExcessCrossWindowPairEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13BranchExcessCrossWindowPairEntry ctx) :=
  (p13BranchExcessComponentEntries ctx).map fun previous =>
    ⟨previous, routeP13BranchExcessCrossWindowPair previous, rfl⟩

theorem p13BranchExcessCrossWindowPairEntries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessCrossWindowPairEntries ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessCrossWindowPairEntries, List.length_map,
    p13BranchExcessComponentEntries_length]

/-- The paired constructor exposes the exact source token, distinct opposite
owner, reverse token, and the common literal edge. -/
theorem pairedRoute_exact
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {entry : P13BranchExcessComponentEntry ctx}
    {residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
      entry.source.2.stub}
    {pair : Routes.InducedPathCrossWindowIncidencePair.CrossWindowIncidencePair
      entry.source.2.stub residual}
    (pairExact : pair = Routes.InducedPathCrossWindowIncidencePair.route
      entry.source.2.stub residual) :
    pair.leftToken = entry.source.2.stub.token ∧
      pair.leftWindow ≠ pair.rightWindow ∧
      pair.leftToken ≠ pair.rightToken ∧
      pair.rightToken.2.2.1 =
        InducedPathWindowLedger.selectedWindow ctx.G.object
          entry.source.2.stub.window entry.source.2.stub.position := by
  subst pair
  exact ⟨
    (Routes.InducedPathCrossWindowIncidencePair.route
      entry.source.2.stub residual).leftTokenExact,
    (Routes.InducedPathCrossWindowIncidencePair.route
      entry.source.2.stub residual).windowsDistinct,
    (Routes.InducedPathCrossWindowIncidencePair.route
      entry.source.2.stub residual).tokensDistinct,
    (Routes.InducedPathCrossWindowIncidencePair.route
      entry.source.2.stub residual).rightTokenNeighbor⟩

end Erdos64EG.Internal
