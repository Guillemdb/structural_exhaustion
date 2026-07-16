import Erdos64EG.P13FixedSkeletonComponentD4
import Erdos64EG.CT15SparsePairResponses
import StructuralExhaustion.Graph.InducedPathComponentD7

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

set_option maxHeartbeats 800000

/-!
# Exact D7 support schedule on component entries

This stage recomputes the already graph-owned sparse-pair activation on the
same minimal context and retains exactly the free-pair supports contained in
each D4 component interface.  It adds no Boolean response and makes no claim
of D5, D6, compatible-context equivalence, or CT8 removal.
-/

abbrev P13ComponentD7Coordinate
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (input : InducedPathComponentBoundarySchedule.Input ctx.G.object) :=
  InducedPathComponentD7.Coordinate (sparsePairActivationStage ctx) input

@[implicit_reducible]
noncomputable def p13ComponentD7Coordinates
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (input : InducedPathComponentBoundarySchedule.Input ctx.G.object) :
    FinEnum (P13ComponentD7Coordinate ctx input) :=
  InducedPathComponentD7.coordinates (sparsePairActivationStage ctx) input

inductive P13BranchExcessD7SupportRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessD4Entry ctx) : Type (u + 1) where
  | evaluated
      (boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object)
      (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
      (inputAnchorExact : input.anchor = boundary)
      (d4 : InducedPathColdSkeleton.TwoStubComponent.DeclaredLocalSemantics
        (InducedPathComponentD1D3Observation.data input)
        (InducedPathComponentD1D3Observation.canonicalPath input))
      (d4Exact : d4 = InducedPathComponentD4.semantics input
        PowerOfTwoLength powerOfTwoLengthDecidable)
      (d7 : FinEnum (P13ComponentD7Coordinate ctx input))
      (d7Exact : d7 = p13ComponentD7Coordinates ctx input)
  | crossWindow
      (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
        entry.previous.previous.source.2.stub)

noncomputable def routeP13BranchExcessD7Support
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessD4Entry ctx) :
    P13BranchExcessD7SupportRoute entry := by
  cases entry.route with
  | evaluated boundary _boundaryTokenExact input inputAnchorExact _observation
      _observationExact d4 d4Exact =>
      exact .evaluated boundary input inputAnchorExact d4 d4Exact
        (p13ComponentD7Coordinates ctx input) rfl
  | crossWindow residual => exact .crossWindow residual

structure P13BranchExcessD7SupportEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  previous : P13BranchExcessD4Entry ctx
  route : P13BranchExcessD7SupportRoute previous
  routeExact : route = routeP13BranchExcessD7Support previous

noncomputable def p13BranchExcessD7SupportEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13BranchExcessD7SupportEntry ctx) :=
  (p13BranchExcessD4Entries ctx).map fun previous =>
    ⟨previous, routeP13BranchExcessD7Support previous, rfl⟩

theorem p13BranchExcessD7SupportEntries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessD7SupportEntries ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessD7SupportEntries, List.length_map,
    p13BranchExcessD4Entries_length]

theorem p13ComponentD7_support_subset
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
    (coordinate : P13ComponentD7Coordinate ctx input) :
    coordinate.support (sparsePairActivationStage ctx) input ⊆
      InducedPathComponentD4.activeSupport input :=
  coordinate.support_subset_active (sparsePairActivationStage ctx) input

end Erdos64EG.Internal
