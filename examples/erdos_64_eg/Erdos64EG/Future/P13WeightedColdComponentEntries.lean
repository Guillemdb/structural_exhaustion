import Erdos64EG.Future.P13WeightedColdBranchExcess
import StructuralExhaustion.Graph.InducedPathBranchExcessComponentEntry

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Auxiliary weighted source to the all-ambient-cubic component route

This maps the graph-owned *all-ambient-cubic* component-entry producer over the
exact node-[152] weighted-cold branch-excess schedule.  It is useful auxiliary
geometry, but it is not the paper's C153.1 route: the paper deletes only the
weighted-cold cubic windows, whereas `InducedPathColdSkeleton` deletes every
ambient-cubic selected window.  In particular a hot ambient-cubic endpoint is
cross-window here but survives the paper's deletion.  The paper-faithful
endpoint split is `P13WeightedColdRestrictedEntries`.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

abbrev P13WeightedColdBranchExcessSource :=
  Sigma fun window : P13WeightedColdCubicWindow ctx node21 =>
    P13WeightedColdBranchExcessStub window

abbrev P13WeightedColdComponentRoute
    (source : P13WeightedColdBranchExcessSource
      (ctx := ctx) (node21 := node21)) :=
  InducedPathBranchExcessComponentEntry.Result
    (p13SelectedWindowCorridorProducer ctx) source.2.stub

/-- One exact node-[152] source paired with the locally computed
delete-all-cold-windows component decision. -/
structure P13WeightedColdComponentEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 3) where
  source : P13WeightedColdBranchExcessSource (ctx := ctx) (node21 := node21)
  route : P13WeightedColdComponentRoute source
  routeExact : route = InducedPathBranchExcessComponentEntry.route
    (p13SelectedWindowCorridorProducer ctx) source.2.stub

/-- Execute one endpoint-membership decision on every exact weighted-cold
source, preserving the node-[152] order. -/
noncomputable def p13WeightedColdComponentEntries :
    List (P13WeightedColdComponentEntry ctx node21) :=
  (p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)).map fun source =>
    ⟨source,
      InducedPathBranchExcessComponentEntry.route
        (p13SelectedWindowCorridorProducer ctx) source.2.stub,
      rfl⟩

theorem p13WeightedColdComponentEntries_length :
    (p13WeightedColdComponentEntries
      (ctx := ctx) (node21 := node21)).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length := by
  simp [p13WeightedColdComponentEntries]

theorem p13WeightedColdComponentEntries_length_eq_thirteen_mul :
    (p13WeightedColdComponentEntries
      (ctx := ctx) (node21 := node21)).length =
      13 * (p13WeightedColdCubicWindows
        (ctx := ctx) (node21 := node21)).length := by
  rw [p13WeightedColdComponentEntries_length,
    p13WeightedColdBranchExcessSchedule_length]

/-- Projecting the adapter output recovers the literal node-[152] source
schedule, not merely a permutation of it. -/
theorem p13WeightedColdComponentEntries_sources :
    (p13WeightedColdComponentEntries
      (ctx := ctx) (node21 := node21)).map
        P13WeightedColdComponentEntry.source =
      p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21) := by
  let sources := p13WeightedColdBranchExcessSchedule
    (ctx := ctx) (node21 := node21)
  change ((sources.map fun source =>
      P13WeightedColdComponentEntry.mk source
        (InducedPathBranchExcessComponentEntry.route
          (p13SelectedWindowCorridorProducer ctx) source.2.stub) rfl).map
      P13WeightedColdComponentEntry.source) = sources
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      change source ::
        ((rest.map fun source =>
          P13WeightedColdComponentEntry.mk source
            (InducedPathBranchExcessComponentEntry.route
              (p13SelectedWindowCorridorProducer ctx) source.2.stub) rfl).map
          P13WeightedColdComponentEntry.source) = source :: rest
      rw [ih]

/-- The adapter retains the exact weighted-cold window of its source stub. -/
theorem P13WeightedColdComponentEntry.sameWindow
    (entry : P13WeightedColdComponentEntry ctx node21) :
    entry.source.2.stub.window =
      p13WeightedWindowIndex entry.source.1.cold.window :=
  entry.source.2.sameWindow

/-- The stored route has exactly the graph producer's two constructors.  This
is an elimination theorem for the adapter output itself, so neither branch can
be selected by an application. -/
theorem P13WeightedColdComponentEntry.route_exhaustive
    (entry : P13WeightedColdComponentEntry ctx node21) :
    (∃ boundary boundaryExact input inputExact,
      entry.route = .component boundary boundaryExact input inputExact) ∨
    (∃ residual, entry.route = .crossWindow residual) := by
  rw [entry.routeExact]
  exact InducedPathBranchExcessComponentEntry.route_exhaustive
    (p13SelectedWindowCorridorProducer ctx) entry.source.2.stub

inductive P13WeightedColdComponentTag
  | component
  | crossWindow
  deriving DecidableEq

def P13WeightedColdComponentEntry.tag
    (entry : P13WeightedColdComponentEntry ctx node21) :
    P13WeightedColdComponentTag :=
  match entry.route with
  | .component _ _ _ _ => .component
  | .crossWindow _ => .crossWindow

noncomputable def p13WeightedColdComponentEntriesWithTag
    (tag : P13WeightedColdComponentTag) :
    List (P13WeightedColdComponentEntry ctx node21) :=
  (p13WeightedColdComponentEntries
    (ctx := ctx) (node21 := node21)).filter fun entry => entry.tag = tag

private theorem twoTagPartitionLength
    (entries : List (P13WeightedColdComponentEntry ctx node21)) :
    (entries.filter fun entry =>
        entry.tag = P13WeightedColdComponentTag.component).length +
      (entries.filter fun entry =>
        entry.tag = P13WeightedColdComponentTag.crossWindow).length =
      entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases tagEquation : entry.tag <;> simp [tagEquation] <;> omega

/-- Every weighted-cold selected incidence enters exactly one of the component
and cross-window ledgers. -/
theorem p13WeightedColdComponentEntries_partition :
    (p13WeightedColdComponentEntriesWithTag
      (ctx := ctx) (node21 := node21) .component).length +
      (p13WeightedColdComponentEntriesWithTag
        (ctx := ctx) (node21 := node21) .crossWindow).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length := by
  rw [p13WeightedColdComponentEntriesWithTag,
    p13WeightedColdComponentEntriesWithTag,
    twoTagPartitionLength,
    p13WeightedColdComponentEntries_length]

/-- A component constructor exposes exactly the same source token and the
complete graph-owned component input anchored at that boundary. -/
theorem component_payload_exact
    (source : P13WeightedColdBranchExcessSource
      (ctx := ctx) (node21 := node21))
    (boundary : InducedPathColdSkeleton.BoundaryStub ctx.G.object)
    (boundaryTokenExact : boundary.token = source.2.stub.token)
    (input : InducedPathComponentBoundarySchedule.Input ctx.G.object)
    (inputAnchorExact : input.anchor = boundary) :
    boundary.token = source.2.stub.token ∧ input.anchor = boundary :=
  ⟨boundaryTokenExact, inputAnchorExact⟩

/-- A cross-window constructor remains indexed by the identical source stub
and retains its deleted-endpoint proof. -/
theorem crossWindow_payload_exact
    (source : P13WeightedColdBranchExcessSource
      (ctx := ctx) (node21 := node21))
    (residual : InducedPathBranchExcessComponentEntry.CrossWindowResidual
      source.2.stub) :
    residual.stubExact = source.2.stub ∧
      source.2.stub.neighbor ∈
        InducedPathColdSkeleton.deletedWindowVertices ctx.G.object :=
  ⟨residual.exact, residual.endpointDeleted⟩

/-- The complete adapter performs one local endpoint-membership test per
source incidence. -/
noncomputable def p13WeightedColdComponentEntryChecks : Nat :=
  (p13WeightedColdComponentEntries
    (ctx := ctx) (node21 := node21)).length

theorem p13WeightedColdComponentEntryChecks_linear :
    p13WeightedColdComponentEntryChecks
      (ctx := ctx) (node21 := node21) ≤
      ctx.G.object.input.vertices.card := by
  have cubicLeCold :
      (p13WeightedColdCubicWindows
        (ctx := ctx) (node21 := node21)).length ≤
        (p13SequentialWeightedColdWindows ctx node21).length := by
    have partition := p13WeightedCold_cubic_nonCubic_length
      (ctx := ctx) (node21 := node21)
    omega
  have coldLePacking :
      (p13SequentialWeightedColdWindows ctx node21).length ≤ p13 ctx := by
    have partition := p13SequentialWeightedHotCount_add_coldCount ctx node21
    omega
  calc
    p13WeightedColdComponentEntryChecks
        (ctx := ctx) (node21 := node21) =
        13 * (p13WeightedColdCubicWindows
          (ctx := ctx) (node21 := node21)).length :=
      p13WeightedColdComponentEntries_length_eq_thirteen_mul
    _ ≤ 13 * p13 ctx := Nat.mul_le_mul_left 13
      (cubicLeCold.trans coldLePacking)
    _ ≤ ctx.G.object.input.vertices.card :=
      thirteen_mul_p13_le_vertexCount ctx

end Erdos64EG.Internal
