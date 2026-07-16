import Erdos64EG.P13FixedSkeletonComponentD1D3
import StructuralExhaustion.Graph.InducedPathComponentD4

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Graph-owned D4 family on every exact component observation

This consumes the D1--D3 ledger without changing its branch.  On each observed
component it constructs the finite internal-wedge family and its literal P13
curvature response relative to the two boundary windows.  Cross-window
residuals pass unchanged.  D5--D7 and all-context equivalence remain separate
typed obligations.
-/

inductive P13BranchExcessD4Route
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessD1D3Entry ctx) : Type (u + 1) where
  | evaluated
      (boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object)
      (boundaryTokenExact : boundary.token = entry.previous.source.2.stub.token)
      (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
      (inputAnchorExact : input.anchor = boundary)
      (observation : InducedPathComponentD1D3Observation.OneStateResidual input
        PowerOfTwoLength powerOfTwoLengthDecidable)
      (observationExact : observation =
        InducedPathComponentD1D3Observation.run input PowerOfTwoLength
          powerOfTwoLengthDecidable)
      (d4 : InducedPathColdSkeleton.TwoStubComponent.DeclaredLocalSemantics
        (InducedPathComponentD1D3Observation.data input)
        (InducedPathComponentD1D3Observation.canonicalPath input))
      (d4Exact : d4 = InducedPathComponentD4.semantics input
        PowerOfTwoLength powerOfTwoLengthDecidable)
  | crossWindow
      (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
        entry.previous.source.2.stub)

noncomputable def routeP13BranchExcessD4
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessD1D3Entry ctx) :
    P13BranchExcessD4Route entry := by
  cases entry.route with
  | observed boundary boundaryTokenExact input inputAnchorExact observation
      observationExact =>
      exact .evaluated boundary boundaryTokenExact input inputAnchorExact
        observation observationExact
        (InducedPathComponentD4.semantics input PowerOfTwoLength
          powerOfTwoLengthDecidable) rfl
  | crossWindow residual => exact .crossWindow residual

structure P13BranchExcessD4Entry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 1) where
  previous : P13BranchExcessD1D3Entry ctx
  route : P13BranchExcessD4Route previous
  routeExact : route = routeP13BranchExcessD4 previous

noncomputable def p13BranchExcessD4Entries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13BranchExcessD4Entry ctx) :=
  (p13BranchExcessD1D3Entries ctx).map fun previous =>
    ⟨previous, routeP13BranchExcessD4 previous, rfl⟩

theorem p13BranchExcessD4Entries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessD4Entries ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessD4Entries, List.length_map,
    p13BranchExcessD1D3Entries_length]

theorem evaluatedRoute_response_provenance
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {entry : P13BranchExcessD1D3Entry ctx}
    {boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object}
    {boundaryTokenExact : boundary.token = entry.previous.source.2.stub.token}
    {input : InducedPathComponentBoundarySchedule.Input ctx.G.object}
    {inputAnchorExact : input.anchor = boundary}
    {observation : InducedPathComponentD1D3Observation.OneStateResidual input
      PowerOfTwoLength powerOfTwoLengthDecidable}
    {observationExact : observation =
      InducedPathComponentD1D3Observation.run input PowerOfTwoLength
        powerOfTwoLengthDecidable}
    {d4 : InducedPathColdSkeleton.TwoStubComponent.DeclaredLocalSemantics
      (InducedPathComponentD1D3Observation.data input)
      (InducedPathComponentD1D3Observation.canonicalPath input)}
    (d4Exact : d4 = InducedPathComponentD4.semantics input
      PowerOfTwoLength powerOfTwoLengthDecidable) :
    d4 = InducedPathComponentD4.semantics input PowerOfTwoLength
        powerOfTwoLengthDecidable ∧
      input.anchor.token = entry.previous.source.2.stub.token ∧
      observation.value = InducedPathComponentD1D3Observation.state input
        PowerOfTwoLength powerOfTwoLengthDecidable ∧
      ∀ coordinate : InducedPathComponentD4.Coordinate input,
        (InducedPathComponentD4.response input PowerOfTwoLength
          powerOfTwoLengthDecidable coordinate = true ↔
        InducedPathAttachment.omegaTwo 13 PowerOfTwoLength
          powerOfTwoLengthDecidable
          (InducedPathComponentD4.attachmentLabel input coordinate.1
            coordinate.2.left)
          (InducedPathComponentD4.attachmentLabel input coordinate.1
            coordinate.2.center)
          (InducedPathComponentD4.attachmentLabel input coordinate.1
            coordinate.2.right) = 1) := by
  have sourceExact : input.anchor.token =
      entry.previous.source.2.stub.token := inputAnchorExact ▸ boundaryTokenExact
  have observationValue : observation.value =
      InducedPathComponentD1D3Observation.state input PowerOfTwoLength
        powerOfTwoLengthDecidable := by
    rw [observationExact]
    rfl
  exact ⟨d4Exact, sourceExact, observationValue,
    InducedPathComponentD4.response_true_iff input PowerOfTwoLength
      powerOfTwoLengthDecidable⟩

theorem evaluatedRoute_localWork
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (input : InducedPathComponentBoundarySchedule.Input ctx.G.object) :
    InducedPathComponentD4.visibleChecks input ≤
      4 * ctx.G.object.input.vertices.card ^ 3 :=
  InducedPathComponentD4.visibleChecks_le_cubic input

end Erdos64EG.Internal
