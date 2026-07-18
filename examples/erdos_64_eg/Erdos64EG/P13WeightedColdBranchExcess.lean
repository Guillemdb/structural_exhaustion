import Erdos64EG.P13SequentialWeightedHotColdLedger
import Erdos64EG.P13SelectedWindowCorridor
import StructuralExhaustion.Graph.InducedPathColdBranchExcess
import Mathlib.Data.List.Nodup

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger
open StructuralExhaustion.Graph.InducedPathColdLedger
open StructuralExhaustion.Graph.InducedPathColdBranchExcess

universe u

/-!
# Weighted-cold P13 windows to the paper's branch-excess schedule

This is the provenance bridge for manuscript nodes `[150]`--`[152]`.  It
starts with exactly the negative entries of the weighted live/cold split,
filters that same list by the graph-owned ambient-cubic predicate, and selects
the thirteen literal branch-excess half-edges of every retained window.

No ambient window family is substituted for the cold family.  Every output
retains its originating `P13SequentialWeightedColdWindow`, including the
aggregate-relative rejection certificate, and all graph computation is
local to that supplied selected window.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Convert the selected packing member carried by the weighted ledger to the
graph framework's index for the identical CT12 packing member. -/
noncomputable def p13WeightedWindowIndex
    (window : P13SelectedConnectorWindow ctx) : WindowIndex ctx.G.object := by
  classical
  refine ⟨window.1, ?_⟩
  change window.1 ∈
    (Graph.InducedPathPacking.windows ctx.G.object 13 (by decide)).toFinset
  exact List.mem_toFinset.mpr window.2

theorem p13WeightedWindowIndex_injective :
    Function.Injective (@p13WeightedWindowIndex ctx) := by
  intro left right equal
  apply Subtype.ext
  have values := congrArg Subtype.val equal
  change left.1 = right.1 at values
  exact values

/-- One weighted-cold window retained by node `[151]`, together with the
computed proof that every one of its thirteen vertices has ambient degree
three. -/
structure P13WeightedColdCubicWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  cold : P13SequentialWeightedColdWindow ctx node21
  cubic : AmbientCubic ctx.G.object (p13WeightedWindowIndex cold.window)

/-- The complementary node-`[151]` entry.  It is retained explicitly so the
ambient-cubic filter is an exact partition rather than an asymptotic slogan. -/
structure P13WeightedColdNonCubicWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  cold : P13SequentialWeightedColdWindow ctx node21
  notCubic : ¬AmbientCubic ctx.G.object (p13WeightedWindowIndex cold.window)

private noncomputable def weightedColdCubicOfList :
    List (P13SequentialWeightedColdWindow ctx node21) →
      List (P13WeightedColdCubicWindow ctx node21)
  | [] => []
  | cold :: tail =>
      letI := ambientCubicDecidable ctx.G.object
        (p13WeightedWindowIndex cold.window)
      if cubic : AmbientCubic ctx.G.object
          (p13WeightedWindowIndex cold.window) then
        ⟨cold, cubic⟩ :: weightedColdCubicOfList tail
      else
        weightedColdCubicOfList tail

private noncomputable def weightedColdNonCubicOfList :
    List (P13SequentialWeightedColdWindow ctx node21) →
      List (P13WeightedColdNonCubicWindow ctx node21)
  | [] => []
  | cold :: tail =>
      letI := ambientCubicDecidable ctx.G.object
        (p13WeightedWindowIndex cold.window)
      if cubic : AmbientCubic ctx.G.object
          (p13WeightedWindowIndex cold.window) then
        weightedColdNonCubicOfList tail
      else
        ⟨cold, cubic⟩ :: weightedColdNonCubicOfList tail

/-- Exact order-preserving ambient-cubic subfamily of the weighted-cold
ledger. -/
noncomputable def p13WeightedColdCubicWindows :
    List (P13WeightedColdCubicWindow ctx node21) :=
  weightedColdCubicOfList (p13SequentialWeightedColdWindows ctx node21)

/-- Exact complementary subfamily discarded by the near-cubic filter. -/
noncomputable def p13WeightedColdNonCubicWindows :
    List (P13WeightedColdNonCubicWindow ctx node21) :=
  weightedColdNonCubicOfList (p13SequentialWeightedColdWindows ctx node21)

private theorem weightedCold_cubic_nonCubic_length
    (windows : List (P13SequentialWeightedColdWindow ctx node21)) :
    (weightedColdCubicOfList windows).length +
      (weightedColdNonCubicOfList windows).length = windows.length := by
  induction windows with
  | nil => rfl
  | cons cold tail ih =>
      simp only [weightedColdCubicOfList, weightedColdNonCubicOfList]
      split <;> simp_all <;> omega

private theorem weightedColdNonCubicOfList_windows_sublist
    (windows : List (P13SequentialWeightedColdWindow ctx node21)) :
    List.Sublist
      ((weightedColdNonCubicOfList windows).map (fun entry => entry.cold.window))
      (windows.map (fun cold => cold.window)) := by
  induction windows with
  | nil => exact .slnil
  | cons cold tail ih =>
      simp only [weightedColdNonCubicOfList, List.map_cons]
      letI := ambientCubicDecidable ctx.G.object
        (p13WeightedWindowIndex cold.window)
      by_cases cubic : AmbientCubic ctx.G.object
          (p13WeightedWindowIndex cold.window)
      · simpa [cubic] using List.Sublist.cons cold.window ih
      · simpa [cubic] using List.Sublist.cons_cons cold.window ih

private theorem weightedColdCubicOfList_windows_sublist
    (windows : List (P13SequentialWeightedColdWindow ctx node21)) :
    List.Sublist
      ((weightedColdCubicOfList windows).map (fun entry => entry.cold.window))
      (windows.map (fun cold => cold.window)) := by
  induction windows with
  | nil => exact .slnil
  | cons cold tail ih =>
      simp only [weightedColdCubicOfList, List.map_cons]
      letI := ambientCubicDecidable ctx.G.object
        (p13WeightedWindowIndex cold.window)
      by_cases cubic : AmbientCubic ctx.G.object
          (p13WeightedWindowIndex cold.window)
      · simpa [cubic] using List.Sublist.cons_cons cold.window ih
      · simpa [cubic] using List.Sublist.cons cold.window ih

/-- The ambient-cubic filtering preserves the no-duplication of the exact
weighted-cold selected-window schedule. -/
theorem p13WeightedColdCubicWindows_nodup :
    (p13WeightedColdCubicWindows
      (ctx := ctx) (node21 := node21)).Nodup := by
  have coldNodup := p13SequentialWeightedColdWindows_window_nodup ctx node21
  have windowNodup :
      ((p13WeightedColdCubicWindows
        (ctx := ctx) (node21 := node21)).map
          (fun entry => entry.cold.window)).Nodup :=
    (weightedColdCubicOfList_windows_sublist
      (p13SequentialWeightedColdWindows ctx node21)).nodup coldNodup
  exact windowNodup.of_map _

/-- Node `[151]` as an exact partition of node `[150]`'s weighted-cold
family. -/
theorem p13WeightedCold_cubic_nonCubic_length :
    (p13WeightedColdCubicWindows (ctx := ctx) (node21 := node21)).length +
      (p13WeightedColdNonCubicWindows (ctx := ctx) (node21 := node21)).length =
        (p13SequentialWeightedColdWindows ctx node21).length := by
  exact weightedCold_cubic_nonCubic_length
    (p13SequentialWeightedColdWindows ctx node21)

/-- Node `[151]`, exact finite payment: every discarded non-cubic
weighted-cold window owns a distinct positive unit of the already inherited
total-surplus ledger. -/
theorem p13WeightedColdNonCubic_length_le_totalSurplus :
    (p13WeightedColdNonCubicWindows
      (ctx := ctx) (node21 := node21)).length ≤
        InducedPathWindowLedger.totalSurplus ctx.G.object := by
  classical
  let entries := p13WeightedColdNonCubicWindows
    (ctx := ctx) (node21 := node21)
  let indices := entries.map fun entry =>
    p13WeightedWindowIndex entry.cold.window
  have coldNodup := p13SequentialWeightedColdWindows_window_nodup ctx node21
  have selectedNodup :
      (entries.map (fun entry => entry.cold.window)).Nodup :=
    (weightedColdNonCubicOfList_windows_sublist
      (p13SequentialWeightedColdWindows ctx node21)).nodup coldNodup
  have indicesNodup : indices.Nodup := by
    simpa [indices, List.map_map, Function.comp_def] using
      selectedNodup.map p13WeightedWindowIndex_injective
  have subset : indices.toFinset ⊆
      nonAmbientCubicWindows ctx.G.object
        (Finset.univ : Finset (WindowIndex ctx.G.object)) := by
    intro index member
    rw [List.mem_toFinset] at member
    rcases List.mem_map.mp member with ⟨entry, entryMember, rfl⟩
    simp only [nonAmbientCubicWindows, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact entry.notCubic
  have baseline : ∀ vertex, 3 ≤ ctx.G.object.degree vertex := fun vertex =>
    ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex)
  calc
    entries.length = indices.toFinset.card := by
      rw [List.toFinset_card_of_nodup indicesNodup]
      simp [indices]
    _ ≤ (nonAmbientCubicWindows ctx.G.object
          (Finset.univ : Finset (WindowIndex ctx.G.object))).card :=
      Finset.card_le_card subset
    _ ≤ InducedPathWindowLedger.totalSurplus ctx.G.object :=
      nonAmbientCubic_card_le_totalSurplus ctx.G.object
        (Finset.univ : Finset (WindowIndex ctx.G.object)) baseline

/-- Node `[151]`, the exact finite square-root form of the manuscript's
`all but o(n)` statement.  The loss is the literal non-cubic cold sublist;
its square is bounded by the exact node-`[21]` near-cubic coefficient times
the selected graph order. -/
theorem p13WeightedColdNonCubic_length_sq_le_nearCubicBudget :
    (p13WeightedColdNonCubicWindows
      (ctx := ctx) (node21 := node21)).length ^ 2 ≤
        surplusScaleCoefficient node21.previous.windowSize
            node21.previous.remainderSize node21.previous.primitiveSize *
          ctx.G.object.input.vertices.card := by
  exact (Nat.pow_le_pow_left
    (p13WeightedColdNonCubic_length_le_totalSurplus
      (ctx := ctx) (node21 := node21)) 2).trans node21.previous.bound

/-- One literal selected excess half-edge, retaining both its weighted-cold
origin and its ambient-cubic proof. -/
structure P13WeightedColdBranchExcessStub
    (window : P13WeightedColdCubicWindow ctx node21) where
  stub : InducedPathColdCorridor.CubicStub ctx.G.object
  selected : stub ∈ branchExcessStubs ctx.G.object
    (p13WeightedWindowIndex window.cold.window) window.cubic

/-- Select precisely the thirteen post-transit stubs prescribed by the paper
for one retained weighted-cold ambient-cubic window. -/
noncomputable def p13WeightedColdBranchExcessStubs
    (window : P13WeightedColdCubicWindow ctx node21) :
    List (P13WeightedColdBranchExcessStub window) :=
  (branchExcessStubs ctx.G.object
      (p13WeightedWindowIndex window.cold.window) window.cubic).attach.map
    fun stub => ⟨stub.1, stub.2⟩

theorem p13WeightedColdBranchExcessStubs_length
    (window : P13WeightedColdCubicWindow ctx node21) :
    (p13WeightedColdBranchExcessStubs window).length = 13 := by
  rw [p13WeightedColdBranchExcessStubs, List.length_map, List.length_attach,
    branchExcessStubs_length_eq_thirteen]

/-- The thirteen branch-excess entries of one retained window are literal
distinct incidences. -/
theorem p13WeightedColdBranchExcessStubs_nodup
    (window : P13WeightedColdCubicWindow ctx node21) :
    (p13WeightedColdBranchExcessStubs window).Nodup := by
  unfold p13WeightedColdBranchExcessStubs
  apply (branchExcessStubs_nodup ctx.G.object
    (p13WeightedWindowIndex window.cold.window) window.cubic).attach.map
  intro left right equal
  apply Subtype.ext
  exact congrArg P13WeightedColdBranchExcessStub.stub equal

theorem P13WeightedColdBranchExcessStub.sameWindow
    {window : P13WeightedColdCubicWindow ctx node21}
    (entry : P13WeightedColdBranchExcessStub window) :
    entry.stub.window = p13WeightedWindowIndex window.cold.window :=
  branchExcessStubs_same_window ctx.G.object
    (p13WeightedWindowIndex window.cold.window) window.cubic
    entry.stub entry.selected

/-- The complete node-`[152]` schedule, ordered first by the exact cold ledger
and then by the local external-incidence order. -/
noncomputable def p13WeightedColdBranchExcessSchedule :
    List (Sigma fun window : P13WeightedColdCubicWindow ctx node21 =>
      P13WeightedColdBranchExcessStub window) :=
  p13WeightedColdCubicWindows.flatMap fun window =>
    (p13WeightedColdBranchExcessStubs window).map fun stub => ⟨window, stub⟩

/-- Node `[152]`: every retained ambient-cubic weighted-cold window contributes
exactly thirteen, with no stub imported from a hot or unrelated window. -/
theorem p13WeightedColdBranchExcessSchedule_length :
    (p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)).length =
      13 * (p13WeightedColdCubicWindows
        (ctx := ctx) (node21 := node21)).length := by
  unfold p13WeightedColdBranchExcessSchedule
  rw [List.length_flatMap]
  simp only [List.length_map, p13WeightedColdBranchExcessStubs_length]
  rw [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
  exact Nat.mul_comm _ _

/-- Every exact node-`[152]` branch-excess incidence occurs once in the
window-major schedule. -/
theorem p13WeightedColdBranchExcessSchedule_nodup :
    (p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)).Nodup := by
  simpa only [p13WeightedColdBranchExcessSchedule, List.sigma] using
    (p13WeightedColdCubicWindows_nodup (ctx := ctx) (node21 := node21)).sigma
      (fun window => p13WeightedColdBranchExcessStubs_nodup window)

/-- Node `[152]`, exact finite form of
`b(𝔖_cold) ≥ 13 C - o(n)`: the only loss is thirteen times the inherited
total-surplus payment for the non-cubic cold windows. -/
theorem thirteen_mul_weightedCold_le_branchExcess_add_surplus :
    13 * (p13SequentialWeightedColdWindows ctx node21).length ≤
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length +
        13 * InducedPathWindowLedger.totalSurplus ctx.G.object := by
  have partition := p13WeightedCold_cubic_nonCubic_length
    (ctx := ctx) (node21 := node21)
  have nonCubicBound := p13WeightedColdNonCubic_length_le_totalSurplus
    (ctx := ctx) (node21 := node21)
  rw [p13WeightedColdBranchExcessSchedule_length]
  omega

/-- The proof-carrying finite output of nodes `[151]`--`[152]`.  It records
the exact loss, its inherited square-root budget, and the branch-excess
payment.  Later density accounting can consume this structure without
reopening the selected-window scan. -/
structure P13WeightedColdNearCubicPayment
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  loss : Nat
  loss_exact : loss = (p13WeightedColdNonCubicWindows
    (ctx := ctx) (node21 := node21)).length
  loss_sq_le : loss ^ 2 ≤
    surplusScaleCoefficient node21.previous.windowSize
        node21.previous.remainderSize node21.previous.primitiveSize *
      ctx.G.object.input.vertices.card
  branch_excess : 13 * (p13SequentialWeightedColdWindows ctx node21).length ≤
    (p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)).length + 13 * loss

/-- Construct the node-`[151]`/`[152]` payment from the exact node-`[21]`
predecessor and no additional hypothesis. -/
noncomputable def verifiedP13WeightedColdNearCubicPayment :
    P13WeightedColdNearCubicPayment ctx node21 := by
  let loss := (p13WeightedColdNonCubicWindows
    (ctx := ctx) (node21 := node21)).length
  refine ⟨loss, rfl,
    p13WeightedColdNonCubic_length_sq_le_nearCubicBudget, ?_⟩
  have partition := p13WeightedCold_cubic_nonCubic_length
    (ctx := ctx) (node21 := node21)
  rw [p13WeightedColdBranchExcessSchedule_length]
  simp only [loss]
  omega

/-- Execute the paper's graph-owned outside-component corridor on the exact
selected branch-excess half-edge.  This is the typed handoff from node `[152]`
to node `[153]`; the later F1--F5 semantic refinement remains node `[153]`'s
own responsibility. -/
noncomputable def P13WeightedColdBranchExcessStub.corridor
    {window : P13WeightedColdCubicWindow ctx node21}
    (entry : P13WeightedColdBranchExcessStub window) :
    P13SelectedWindowFirstFailure ctx entry.stub :=
  InducedPathColdCorridor.runFirstFailure
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable entry.stub

end Erdos64EG.Internal
