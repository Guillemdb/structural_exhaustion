import Erdos64EG.Future.P13FixedSkeletonEntrySchedule
import StructuralExhaustion.Core.ExactHandoff
import Erdos64EG.Future.P13SelectedWindowCorridor
import StructuralExhaustion.Graph.InducedPathColdBranchExcess

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger
open StructuralExhaustion.Graph.InducedPathColdLedger
open StructuralExhaustion.Graph.InducedPathColdBranchExcess

universe u

/-!
# Fixed-skeleton branch-excess corridor schedule

This is the graph-owned implementation of the manuscript step following the
exact `15 - 2 = 13` cold-window calculation.  It filters the exact CT12 window
order to ambient-cubic windows, selects all thirteen literal branch-excess
half-edges of each retained window, and executes the canonical deleted-edge
first-failure corridor on every selected half-edge.

No cold family, outcome tag, path, context, or state collection is accepted
from a caller.  The only input is the verified node-`[21]` predecessor, used
for provenance; every schedule below is recomputed from its selected graph.
-/

abbrev P13AmbientCubicWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {window : WindowIndex ctx.G.object // AmbientCubic ctx.G.object window}

/-- Exact order-preserving ambient-cubic filter of the CT12 window schedule. -/
@[implicit_reducible]
noncomputable def p13AmbientCubicWindows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    FinEnum (P13AmbientCubicWindow ctx) :=
  Core.Enumeration.subtype (windowIndices ctx.G.object)
    (AmbientCubic ctx.G.object) (ambientCubicDecidable ctx.G.object)

/-- The exact retained ambient-cubic family loses at most the already
computed total-surplus ledger.  This is the finite, graph-owned form of the
paper's near-cubic filtering step: the source family is the literal CT12
packing, and every discarded window contains a distinct positive window
surplus unit. -/
theorem p13_le_ambientCubic_add_totalSurplus
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13 ctx ≤ (p13AmbientCubicWindows ctx).card +
      totalSurplus ctx.G.object := by
  letI : FinEnum (WindowIndex ctx.G.object) := windowIndices ctx.G.object
  have retained := cold_card_le_ambientCubic_add_windowSurplus
    ctx.G.object (Finset.univ : Finset (WindowIndex ctx.G.object))
    (fun vertex =>
      ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))
  rw [Finset.card_univ, ← FinEnum.card_eq_fintypeCard,
    windowIndex_card_eq_packingNumber] at retained
  have cubicCard :
      (ambientCubicWindows ctx.G.object
        (Finset.univ : Finset (WindowIndex ctx.G.object))).card =
        (p13AmbientCubicWindows ctx).card := by
    classical
    rw [p13AmbientCubicWindows,
      Core.Enumeration.subtype_card_eq_filter]
    unfold ambientCubicWindows
    congr 1
    ext window
    simp
  rw [cubicCard] at retained
  have surplusLe : windowSurplus ctx.G.object ≤ totalSurplus ctx.G.object := by
    rw [windowSurplus_eq_coveredSurplus]
    have partition := covered_add_remainder_eq_totalSurplus ctx.G.object
    omega
  exact retained.trans (Nat.add_le_add_left surplusLe
    (p13AmbientCubicWindows ctx).card)

/-- One literal selected excess half-edge and its computed first-failure
corridor, all tied to the same ambient-cubic window. -/
structure P13BranchExcessCorridor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) where
  stub : InducedPathColdCorridor.CubicStub ctx.G.object
  selected : stub ∈ branchExcessStubs ctx.G.object window.1 window.2
  result : P13SelectedWindowFirstFailure ctx stub
  resultExact : result = InducedPathColdCorridor.runFirstFailure
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable stub

/-- Run the paper's corridor classifier on all thirteen selected excess
half-edges of one ambient-cubic window. -/
noncomputable def p13WindowBranchExcessCorridors
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    List (P13BranchExcessCorridor ctx window) :=
  (branchExcessStubs ctx.G.object window.1 window.2).attach.map fun stub =>
    { stub := stub.1
      selected := stub.2
      result := InducedPathColdCorridor.runFirstFailure
        (p13SelectedWindowCorridorProducer ctx)
        PowerOfTwoLength powerOfTwoLengthDecidable stub.1
      resultExact := rfl }

theorem p13WindowBranchExcessCorridors_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowBranchExcessCorridors ctx window).length = 13 := by
  rw [p13WindowBranchExcessCorridors, List.length_map, List.length_attach,
    branchExcessStubs_length_eq_thirteen]

theorem P13BranchExcessCorridor.sameWindow
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) :
    corridor.stub.window = window.1 :=
  branchExcessStubs_same_window ctx.G.object window.1 window.2
    corridor.stub corridor.selected

/-- The three realizable constructors of the current graph-owned F1--F5
runner.  F2 and F3 are not relabelled: their data types are empty until the
paper's compatible-context and smaller-replacement producers are installed. -/
inductive P13BranchExcessOutcomeTag
  | targetHit
  | surplus
  | germ
  deriving DecidableEq

def P13BranchExcessCorridor.outcomeTag
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) :
    P13BranchExcessOutcomeTag :=
  match corridor.result with
  | .first _ (.f1 _ _) => .targetHit
  | .first _ (.f2 _ _ impossible) => nomatch impossible
  | .first _ (.f3 _ _ _ impossible) => nomatch impossible
  | .first _ (.f4 _ _ _ _ _) => .surplus
  | .germ _ _ => .germ

/-- Global selected-half-edge schedule in the inherited cubic-window order. -/
noncomputable def p13BranchExcessCorridors
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (Sigma fun window : P13AmbientCubicWindow ctx =>
      P13BranchExcessCorridor ctx window) :=
  (p13AmbientCubicWindows ctx).orderedValues.flatMap fun window =>
    (p13WindowBranchExcessCorridors ctx window).map fun corridor =>
      ⟨window, corridor⟩

/-- Exact constructor subledger of the already computed global schedule. -/
noncomputable def p13BranchExcessCorridorsWithTag
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (tag : P13BranchExcessOutcomeTag) :
    List (Sigma fun window : P13AmbientCubicWindow ctx =>
      P13BranchExcessCorridor ctx window) :=
  (p13BranchExcessCorridors ctx).filter fun corridor =>
    corridor.2.outcomeTag = tag

private theorem threeTagPartitionLength
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (corridors : List (Sigma fun window : P13AmbientCubicWindow ctx =>
      P13BranchExcessCorridor ctx window)) :
    (corridors.filter fun corridor =>
        corridor.2.outcomeTag = P13BranchExcessOutcomeTag.targetHit).length +
      (corridors.filter fun corridor =>
        corridor.2.outcomeTag = P13BranchExcessOutcomeTag.surplus).length +
      (corridors.filter fun corridor =>
        corridor.2.outcomeTag = P13BranchExcessOutcomeTag.germ).length =
      corridors.length := by
  induction corridors with
  | nil => rfl
  | cons corridor rest ih =>
      cases tagEquation : corridor.2.outcomeTag <;>
        simp [tagEquation] <;> omega

set_option maxHeartbeats 800000 in
/-- There are exactly thirteen computed corridor entries per retained
ambient-cubic window. -/
theorem p13BranchExcessCorridors_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessCorridors ctx).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  unfold p13BranchExcessCorridors
  rw [List.length_flatMap]
  simp only [List.length_map, p13WindowBranchExcessCorridors_length]
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul,
    FinEnum.orderedValues_length]
  exact Nat.mul_comm _ _

/-- Every selected branch-excess half-edge is accounted for exactly once as
an F1 target hit, an F4 surplus handoff, or an F5 structural germ. -/
theorem p13BranchExcessCorridors_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BranchExcessCorridorsWithTag ctx .targetHit).length +
      (p13BranchExcessCorridorsWithTag ctx .surplus).length +
      (p13BranchExcessCorridorsWithTag ctx .germ).length =
      13 * (p13AmbientCubicWindows ctx).card := by
  rw [p13BranchExcessCorridorsWithTag,
    p13BranchExcessCorridorsWithTag,
    p13BranchExcessCorridorsWithTag,
    threeTagPartitionLength,
    p13BranchExcessCorridors_length]

/-! ## Local work bound -/

noncomputable def p13BranchExcessCorridorCheck
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) : Nat :=
  ((p13SelectedWindowCorridorProducer ctx).ambientReturn
    corridor.stub).support.length

theorem p13BranchExcessCorridorCheck_le_vertices
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    (corridor : P13BranchExcessCorridor ctx window) :
    p13BranchExcessCorridorCheck corridor ≤
      ctx.G.object.input.vertices.card := by
  unfold p13BranchExcessCorridorCheck
  simpa only [FinEnum.orderedValues_length] using
    Core.Enumeration.length_le_elems_of_nodup
      ctx.G.object.input.vertices
      (((p13SelectedWindowCorridorProducer ctx).ambientReturn_isPath
        corridor.stub).support_nodup)

/-- Sum of the actual stored corridor-stage lengths.  This charges only the
thirteen selected excess stubs of each retained cubic window. -/
noncomputable def p13BranchExcessCorridorChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  ((p13BranchExcessCorridors ctx).map fun corridor =>
    p13BranchExcessCorridorCheck corridor.2).sum

/-- Every proof-carrying return is a simple path, so the complete selected
corridor ledger has a quadratic bound in the ambient vertex count.  No
ambient path family is generated to establish this bound. -/
theorem p13BranchExcessCorridorChecks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13BranchExcessCorridorChecks ctx ≤
      ctx.G.object.input.vertices.card ^ 2 := by
  let entries := p13BranchExcessCorridors ctx
  let n := ctx.G.object.input.vertices.card
  have each : ∀ entry ∈ entries,
      p13BranchExcessCorridorCheck entry.2 ≤ n := by
    intro entry _member
    exact p13BranchExcessCorridorCheck_le_vertices entry.2
  have sumBound :
      (entries.map fun entry =>
        p13BranchExcessCorridorCheck entry.2).sum ≤
        entries.length * n := by
    calc
      (entries.map fun entry =>
          p13BranchExcessCorridorCheck entry.2).sum ≤
          (entries.map fun _entry => n).sum := by
        exact List.sum_le_sum fun entry member => each entry member
      _ = entries.length * n := by
        rw [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
  have cubicLe : (p13AmbientCubicWindows ctx).card ≤ p13 ctx := by
    have subtypeLe := Core.Enumeration.subtype_card_le
      (windowIndices ctx.G.object) (AmbientCubic ctx.G.object)
      (ambientCubicDecidable ctx.G.object)
    rw [windowIndex_card_eq_packingNumber] at subtypeLe
    exact subtypeLe
  have selectedLe : 13 * (p13AmbientCubicWindows ctx).card ≤ n := by
    exact (Nat.mul_le_mul_left 13 cubicLe).trans
      (thirteen_mul_p13_le_vertexCount ctx)
  calc
    p13BranchExcessCorridorChecks ctx =
        (entries.map fun entry =>
          p13BranchExcessCorridorCheck entry.2).sum := rfl
    _ ≤ entries.length * n := sumBound
    _ = (13 * (p13AmbientCubicWindows ctx).card) * n := by
      rw [p13BranchExcessCorridors_length]
    _ ≤ n * n := Nat.mul_le_mul_right n selectedLe
    _ = n ^ 2 := by ring

/-- Node-`[21]` provenance wrapper.  The corridor list is deliberately not a
field and therefore cannot be supplied by an application. -/
structure VerifiedP13BranchExcessCorridorPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4)
    extends Core.ExactHandoff node21 where

def verifiedP13BranchExcessCorridorPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    VerifiedP13BranchExcessCorridorPrefix ctx node21 := ⟨⟨node21, rfl⟩⟩

namespace VerifiedP13BranchExcessCorridorPrefix

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable def corridors
    (_prefix : VerifiedP13BranchExcessCorridorPrefix ctx node21) :=
  p13BranchExcessCorridors ctx

theorem corridors_length
    (verified : VerifiedP13BranchExcessCorridorPrefix ctx node21) :
    verified.corridors.length = 13 * (p13AmbientCubicWindows ctx).card :=
  p13BranchExcessCorridors_length ctx

end VerifiedP13BranchExcessCorridorPrefix

end Erdos64EG.Internal
