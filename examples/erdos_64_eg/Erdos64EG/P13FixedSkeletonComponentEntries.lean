import Erdos64EG.P13FixedSkeletonBranchExcessCorridors
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Exact component entry for every selected branch-excess incidence

This stage corrects the corridor boundary before any F2--F5 semantics are
attempted.  Each literal branch-excess stub is tested once.  If its endpoint
survives deletion of the ambient-cubic selected windows, the graph layer
constructs the exact `InducedPathComponentBoundarySchedule.Input`; its stored
incident schedule, true cyclic successor, and BFS component path are therefore
available.  A stub ending in another deleted window is retained as a typed
cross-window residual.

The stage uses the complete thirteen-per-window schedule from its predecessor.
It does not call the weaker deleted-edge-return F1/F4/F5 classifier and does
not enumerate paths, components, states, responses, or contexts.
-/

abbrev P13BranchExcessComponentRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (source : P13BranchExcessCorridor ctx window) :=
  InducedPathBranchExcessComponentEntry.Result
    (p13SelectedWindowCorridorProducer ctx) source.stub

/-- One source incidence paired with its exact component-entry decision. -/
structure P13BranchExcessComponentEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type u where
  source : Sigma fun window : P13AmbientCubicWindow ctx =>
    P13BranchExcessCorridor ctx window
  route : P13BranchExcessComponentRoute source.2
  routeExact : route = InducedPathBranchExcessComponentEntry.route
    (p13SelectedWindowCorridorProducer ctx) source.2.stub

/-- Execute the local endpoint dichotomy on every predecessor incidence. -/
noncomputable def p13BranchExcessComponentEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13BranchExcessComponentEntry ctx) :=
  (p13BranchExcessCorridors ctx).map fun source =>
    ⟨source,
      InducedPathBranchExcessComponentEntry.route
        (p13SelectedWindowCorridorProducer ctx) source.2.stub,
      rfl⟩

theorem p13BranchExcessComponentEntries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessComponentEntries ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessComponentEntries, List.length_map,
    p13BranchExcessCorridors_length]

inductive P13BranchExcessComponentTag
  | component
  | crossWindow
  deriving DecidableEq

def P13BranchExcessComponentEntry.tag
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}} :
    P13BranchExcessComponentEntry ctx -> P13BranchExcessComponentTag
  | ⟨_, .component _ _ _ _, _⟩ => .component
  | ⟨_, .crossWindow _, _⟩ => .crossWindow

theorem P13BranchExcessComponentEntry.tag_crossWindow_of_route_eq
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {entry : P13BranchExcessComponentEntry ctx}
    {residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
      entry.source.2.stub}
    (routeExact : entry.route = .crossWindow residual) :
    entry.tag = .crossWindow := by
  cases entry with
  | mk source route storedExact =>
      cases route with
      | component boundary boundaryExact input inputExact =>
          contradiction
      | crossWindow actualResidual => rfl

noncomputable def p13BranchExcessComponentEntriesWithTag
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (tag : P13BranchExcessComponentTag) :
    List (P13BranchExcessComponentEntry ctx) :=
  (p13BranchExcessComponentEntries ctx).filter fun entry => entry.tag = tag

private theorem twoTagPartitionLength
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entries : List (P13BranchExcessComponentEntry ctx)) :
    (entries.filter fun entry =>
        entry.tag = P13BranchExcessComponentTag.component).length +
      (entries.filter fun entry =>
        entry.tag = P13BranchExcessComponentTag.crossWindow).length =
      entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases tagEquation : entry.tag <;>
        simp [tagEquation] <;> omega

/-- Every one of the thirteen selected incidences enters exactly one of the
component-corridor and cross-window ledgers. -/
theorem p13BranchExcessComponentEntries_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessComponentEntriesWithTag ctx .component).length +
      (p13BranchExcessComponentEntriesWithTag ctx .crossWindow).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessComponentEntriesWithTag,
    p13BranchExcessComponentEntriesWithTag,
    twoTagPartitionLength,
    p13BranchExcessComponentEntries_length]

/-- The component constructor exposes precisely the paper's structural
corridor predecessor: the literal source token, complete component schedule,
true cyclic successor, and one computed shortest component path. -/
theorem componentRoute_structuralCorridor
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (source : P13BranchExcessCorridor ctx window)
    (boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object)
    (boundaryTokenExact : boundary.token = source.stub.token)
    (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
    (inputAnchorExact : input.anchor = boundary) :
    input.anchor.token = source.stub.token ∧
      2 ≤ (InducedPathComponentBoundarySchedule.incidentStubs input).length ∧
      (InducedPathComponentBoundarySchedule.twoStubComponent input).successor =
        @List.next _
          (InducedPathComponentBoundarySchedule.boundaryStubs
            ctx.G.object).decEq
          (InducedPathComponentBoundarySchedule.incidentStubs input)
          input.anchor
          (InducedPathComponentBoundarySchedule.anchor_mem_incidentStubs input) ∧
      (InducedPathComponentBoundarySchedule.twoStubComponent input).successor ≠
        input.anchor ∧
      InducedPathColdSkeleton.component
          (InducedPathComponentBoundarySchedule.twoStubComponent input).successor =
        InducedPathColdSkeleton.component input.anchor ∧
      (InducedPathComponentBoundarySchedule.componentPath input).IsPath ∧
      (InducedPathComponentBoundarySchedule.componentPath input).length =
        (InducedPathColdSkeleton.component input.anchor).toSimpleGraph.dist
          (InducedPathComponentBoundarySchedule.twoStubComponent input).componentRoot
          (InducedPathComponentBoundarySchedule.twoStubComponent input).componentTarget := by
  subst boundary
  exact ⟨boundaryTokenExact,
    InducedPathComponentBoundarySchedule.two_le_incidentStubs_length input,
    rfl,
    (InducedPathComponentBoundarySchedule.twoStubComponent input).distinct,
    (InducedPathComponentBoundarySchedule.twoStubComponent input).sameComponent,
    InducedPathComponentBoundarySchedule.componentPath_isPath input,
    InducedPathComponentBoundarySchedule.componentPath_shortest input⟩

/-- One endpoint-membership check per exact predecessor incidence. -/
noncomputable def p13BranchExcessComponentEntryChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat := (p13BranchExcessComponentEntries ctx).length

theorem p13BranchExcessComponentEntryChecks_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13BranchExcessComponentEntryChecks ctx <=
      ctx.G.object.input.vertices.card := by
  have cubicLe : (p13AmbientCubicWindows ctx).card <= p13 ctx := by
    have bound := Core.Enumeration.subtype_card_le
      (InducedPathWindowLedger.windowIndices ctx.G.object)
      (InducedPathColdLedger.AmbientCubic ctx.G.object)
      (InducedPathColdLedger.ambientCubicDecidable ctx.G.object)
    rw [InducedPathWindowLedger.windowIndex_card_eq_packingNumber] at bound
    exact bound
  calc
    p13BranchExcessComponentEntryChecks ctx =
        13 * (p13AmbientCubicWindows ctx).card := by
      exact p13BranchExcessComponentEntries_length ctx
    _ <= 13 * p13 ctx := Nat.mul_le_mul_left 13 cubicLe
    _ <= ctx.G.object.input.vertices.card := thirteen_mul_p13_le_vertexCount ctx

/-- Exact node-21 provenance.  Neither the entry schedule nor its routes are
caller fields. -/
structure VerifiedP13BranchExcessComponentPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u
    extends Core.ExactHandoff node21 where

def verifiedP13BranchExcessComponentPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    VerifiedP13BranchExcessComponentPrefix ctx node21 := ⟨⟨node21, rfl⟩⟩

namespace VerifiedP13BranchExcessComponentPrefix

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable def entries
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21) :=
  p13BranchExcessComponentEntries ctx

theorem entries_partition
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21) :
    (p13BranchExcessComponentEntriesWithTag ctx .component).length +
      (p13BranchExcessComponentEntriesWithTag ctx .crossWindow).length =
      13 * (p13AmbientCubicWindows ctx).card :=
  p13BranchExcessComponentEntries_partition ctx

end VerifiedP13BranchExcessComponentPrefix

end Erdos64EG.Internal
