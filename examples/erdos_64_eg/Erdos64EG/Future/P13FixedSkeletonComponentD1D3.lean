import Erdos64EG.Future.P13FixedSkeletonComponentEntries
import StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# D1--D3 observation on every exact component entry

The component-entry predecessor owns the complete boundary schedule, cyclic
successor, and computed shortest component path.  This stage projects exactly
the boundary degrees, two P13 offsets, connector length, and thirteen target
offset bits already implemented by the graph layer.  It retains the typed
`MissingD4D7Reconstruction` marker; no D4--D7 or compatible-context semantics
are asserted.
-/

inductive P13BranchExcessD1D3Route
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessComponentEntry ctx) : Type u where
  | observed
      (boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object)
      (boundaryTokenExact : boundary.token = entry.source.2.stub.token)
      (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
      (inputAnchorExact : input.anchor = boundary)
      (observation : InducedPathComponentD1D3Observation.OneStateResidual input
        PowerOfTwoLength powerOfTwoLengthDecidable)
      (observationExact : observation =
        InducedPathComponentD1D3Observation.run input PowerOfTwoLength
          powerOfTwoLengthDecidable)
  | crossWindow
      (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
        entry.source.2.stub)

/-- Consume the exact component-entry constructor and run the existing
graph-owned D1--D3 projection only on its component side. -/
noncomputable def routeP13BranchExcessD1D3
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : P13BranchExcessComponentEntry ctx) :
    P13BranchExcessD1D3Route entry := by
  cases entry.route with
  | component boundary boundaryTokenExact input inputAnchorExact =>
      exact .observed boundary boundaryTokenExact input inputAnchorExact
        (InducedPathComponentD1D3Observation.run input PowerOfTwoLength
          powerOfTwoLengthDecidable) rfl
  | crossWindow residual => exact .crossWindow residual

/-- One exact predecessor entry and its computed D1--D3 route. -/
structure P13BranchExcessD1D3Entry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type u where
  previous : P13BranchExcessComponentEntry ctx
  route : P13BranchExcessD1D3Route previous
  routeExact : route = routeP13BranchExcessD1D3 previous

noncomputable def p13BranchExcessD1D3Entries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13BranchExcessD1D3Entry ctx) :=
  (p13BranchExcessComponentEntries ctx).map fun previous =>
    ⟨previous, routeP13BranchExcessD1D3 previous, rfl⟩

theorem p13BranchExcessD1D3Entries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessD1D3Entries ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessD1D3Entries, List.length_map,
    p13BranchExcessComponentEntries_length]

theorem observedRoute_has_exact_D1D3
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {entry : P13BranchExcessComponentEntry ctx}
    {boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object}
    {boundaryTokenExact : boundary.token = entry.source.2.stub.token}
    {input : InducedPathComponentBoundarySchedule.Input ctx.G.object}
    {inputAnchorExact : input.anchor = boundary}
    {observation : InducedPathComponentD1D3Observation.OneStateResidual input
      PowerOfTwoLength powerOfTwoLengthDecidable}
    (observationExact : observation =
      InducedPathComponentD1D3Observation.run input PowerOfTwoLength
        powerOfTwoLengthDecidable) :
    input.anchor.token = entry.source.2.stub.token ∧
      observation.value = InducedPathComponentD1D3Observation.state input
        PowerOfTwoLength powerOfTwoLengthDecidable ∧
      Nonempty (InducedPathColdSkeleton.TwoStubComponent.MissingD4D7Reconstruction
        (InducedPathComponentD1D3Observation.data input)
        (InducedPathComponentD1D3Observation.canonicalPath input)) := by
  subst observation
  exact ⟨inputAnchorExact ▸ boundaryTokenExact, rfl,
    ⟨(InducedPathComponentD1D3Observation.run input
      PowerOfTwoLength powerOfTwoLengthDecidable).missing⟩⟩

/-- Quadratic visible envelope: at most `n` exact entries, with two degree
rows and thirteen fixed target-offset bits on each component entry. -/
noncomputable def p13BranchExcessD1D3VisibleChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat := (p13BranchExcessD1D3Entries ctx).length *
      (2 * ctx.G.object.input.vertices.card + 13)

theorem p13BranchExcessD1D3VisibleChecks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13BranchExcessD1D3VisibleChecks ctx ≤
      15 * (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  let n := ctx.G.object.input.vertices.card
  have entriesLe : (p13BranchExcessD1D3Entries ctx).length ≤ n := by
    have bound := p13BranchExcessComponentEntryChecks_linear ctx
    simpa [p13BranchExcessComponentEntryChecks,
      p13BranchExcessD1D3Entries, p13BranchExcessComponentEntries] using bound
  unfold p13BranchExcessD1D3VisibleChecks
  dsimp only [n] at entriesLe ⊢
  calc
    (p13BranchExcessD1D3Entries ctx).length *
        (2 * ctx.G.object.input.vertices.card + 13) ≤
      ctx.G.object.input.vertices.card *
        (2 * ctx.G.object.input.vertices.card + 13) :=
      Nat.mul_le_mul_right _ entriesLe
    _ ≤ 15 * (ctx.G.object.input.vertices.card + 1) ^ 2 := by
      nlinarith

end Erdos64EG.Internal
