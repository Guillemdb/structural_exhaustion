import Erdos64EG.Node150
import StructuralExhaustion.Graph.InducedPathColdBranchExcess
import Mathlib.Data.List.Nodup

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger
open StructuralExhaustion.Graph.InducedPathColdLedger

universe u

/-!
# Diagram node [151]: ambient-cubic filtering of the cold residual

Node [151] consumes the exact node-[150] cold residual.  It performs only the
local near-cubic filter prescribed by the graph framework: the same sequential
weighted-cold windows are partitioned into ambient-cubic and non-cubic
windows, and the discarded non-cubic sublist is paid by the inherited
node-[21] surplus budget.
-/

noncomputable def node151WindowIndex
    {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual)
    (window : P13SelectedConnectorWindow (Node21Context active.node18)) :
    WindowIndex (Node21Context active.node18).G.object := by
  classical
  refine ⟨window.1, ?_⟩
  change window.1 ∈
    (Graph.InducedPathPacking.windows
      (Node21Context active.node18).G.object 13 (by decide)).toFinset
  exact List.mem_toFinset.mpr window.2

theorem node151WindowIndex_injective {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    Function.Injective (node151WindowIndex active) := by
  intro left right equal
  apply Subtype.ext
  have values := congrArg Subtype.val equal
  change left.1 = right.1 at values
  exact values

private noncomputable def node151ColdCubicOfList {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    List (P13SequentialWeightedColdWindow (Node21Context active.node18)
      active.node21.barrierRateCertificate) →
      List ({ cold : P13SequentialWeightedColdWindow
        (Node21Context active.node18) active.node21.barrierRateCertificate //
          AmbientCubic (Node21Context active.node18).G.object
            (node151WindowIndex active cold.window) })
  | [] => []
  | cold :: tail =>
      letI := ambientCubicDecidable (Node21Context active.node18).G.object
        (node151WindowIndex active cold.window)
      if cubic : AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window) then
        ⟨cold, cubic⟩ :: node151ColdCubicOfList active tail
      else
        node151ColdCubicOfList active tail

private noncomputable def node151ColdNonCubicOfList {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    List (P13SequentialWeightedColdWindow (Node21Context active.node18)
      active.node21.barrierRateCertificate) →
      List ({ cold : P13SequentialWeightedColdWindow
        (Node21Context active.node18) active.node21.barrierRateCertificate //
          ¬AmbientCubic (Node21Context active.node18).G.object
            (node151WindowIndex active cold.window) })
  | [] => []
  | cold :: tail =>
      letI := ambientCubicDecidable (Node21Context active.node18).G.object
        (node151WindowIndex active cold.window)
      if cubic : AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window) then
        node151ColdNonCubicOfList active tail
      else
        ⟨cold, cubic⟩ :: node151ColdNonCubicOfList active tail

noncomputable def node151ColdCubicWindows {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    List ({ cold : P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate //
        AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window) }) :=
  node151ColdCubicOfList active
    (p13SequentialWeightedColdWindows (Node21Context active.node18)
      active.node21.barrierRateCertificate)

noncomputable def node151ColdNonCubicWindows {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    List ({ cold : P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate //
        ¬AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window) }) :=
  node151ColdNonCubicOfList active
    (p13SequentialWeightedColdWindows (Node21Context active.node18)
      active.node21.barrierRateCertificate)

private theorem node151Cold_cubic_nonCubic_length_ofList {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual)
    (windows : List (P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate)) :
    (node151ColdCubicOfList active windows).length +
      (node151ColdNonCubicOfList active windows).length = windows.length := by
  induction windows with
  | nil => rfl
  | cons cold tail ih =>
      simp only [node151ColdCubicOfList, node151ColdNonCubicOfList]
      split <;> simp_all <;> omega

private theorem node151ColdCubicOfList_windows_sublist {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual)
    (windows : List (P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate)) :
    List.Sublist
      ((node151ColdCubicOfList active windows).map
        (fun entry => entry.1.window))
      (windows.map (fun cold => cold.window)) := by
  induction windows with
  | nil => exact .slnil
  | cons cold tail ih =>
      simp only [node151ColdCubicOfList, List.map_cons]
      letI := ambientCubicDecidable (Node21Context active.node18).G.object
        (node151WindowIndex active cold.window)
      by_cases cubic : AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window)
      · simpa [cubic] using List.Sublist.cons_cons cold.window ih
      · simpa [cubic] using List.Sublist.cons cold.window ih

private theorem node151ColdNonCubicOfList_windows_sublist {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual)
    (windows : List (P13SequentialWeightedColdWindow
      (Node21Context active.node18) active.node21.barrierRateCertificate)) :
    List.Sublist
      ((node151ColdNonCubicOfList active windows).map
        (fun entry => entry.1.window))
      (windows.map (fun cold => cold.window)) := by
  induction windows with
  | nil => exact .slnil
  | cons cold tail ih =>
      simp only [node151ColdNonCubicOfList, List.map_cons]
      letI := ambientCubicDecidable (Node21Context active.node18).G.object
        (node151WindowIndex active cold.window)
      by_cases cubic : AmbientCubic (Node21Context active.node18).G.object
          (node151WindowIndex active cold.window)
      · simpa [cubic] using List.Sublist.cons cold.window ih
      · simpa [cubic] using List.Sublist.cons_cons cold.window ih

theorem node151ColdCubicWindows_nodup {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    (node151ColdCubicWindows active).Nodup := by
  have coldNodup :=
    p13SequentialWeightedColdWindows_window_nodup
      (Node21Context active.node18) active.node21.barrierRateCertificate
  have windowNodup :
      ((node151ColdCubicWindows active).map
        (fun entry => entry.1.window)).Nodup :=
    (node151ColdCubicOfList_windows_sublist active
      (p13SequentialWeightedColdWindows (Node21Context active.node18)
        active.node21.barrierRateCertificate)).nodup coldNodup
  exact windowNodup.of_map _

theorem node151Cold_cubic_nonCubic_length {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    (node151ColdCubicWindows active).length +
      (node151ColdNonCubicWindows active).length =
        node150ColdCount active := by
  exact node151Cold_cubic_nonCubic_length_ofList active
    (p13SequentialWeightedColdWindows (Node21Context active.node18)
      active.node21.barrierRateCertificate)

theorem node151ColdNonCubic_length_le_totalSurplus {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    (node151ColdNonCubicWindows active).length ≤
        InducedPathWindowLedger.totalSurplus
          (Node21Context active.node18).G.object := by
  classical
  let entries := node151ColdNonCubicWindows active
  let indices := entries.map fun entry =>
    node151WindowIndex active entry.1.window
  have coldNodup :=
    p13SequentialWeightedColdWindows_window_nodup
      (Node21Context active.node18) active.node21.barrierRateCertificate
  have selectedNodup :
      (entries.map (fun entry => entry.1.window)).Nodup :=
    (node151ColdNonCubicOfList_windows_sublist active
      (p13SequentialWeightedColdWindows (Node21Context active.node18)
        active.node21.barrierRateCertificate)).nodup coldNodup
  have indicesNodup : indices.Nodup := by
    simpa [indices, List.map_map, Function.comp_def] using
      selectedNodup.map (node151WindowIndex_injective active)
  have subset : indices.toFinset ⊆
      nonAmbientCubicWindows (Node21Context active.node18).G.object
        (Finset.univ :
          Finset (WindowIndex (Node21Context active.node18).G.object)) := by
    intro index member
    rw [List.mem_toFinset] at member
    rcases List.mem_map.mp member with ⟨entry, _entryMember, rfl⟩
    simp only [nonAmbientCubicWindows, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact entry.2
  have baseline : ∀ vertex,
      3 ≤ (Node21Context active.node18).G.object.degree vertex := fun vertex =>
    (Node21Context active.node18).baseline.trans
      ((Node21Context active.node18).G.object.minDegree_le_degree vertex)
  calc
    entries.length = indices.toFinset.card := by
      rw [List.toFinset_card_of_nodup indicesNodup]
      simp [indices]
    _ ≤ (nonAmbientCubicWindows (Node21Context active.node18).G.object
          (Finset.univ :
            Finset (WindowIndex (Node21Context active.node18).G.object))).card :=
      Finset.card_le_card subset
    _ ≤ InducedPathWindowLedger.totalSurplus
          (Node21Context active.node18).G.object :=
      nonAmbientCubic_card_le_totalSurplus
        (Node21Context active.node18).G.object
        (Finset.univ :
          Finset (WindowIndex (Node21Context active.node18).G.object)) baseline

theorem node151ColdNonCubic_length_sq_le_nearCubicBudget {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    (node151ColdNonCubicWindows active).length ^ 2 ≤
      node19SurplusCoefficient *
        (Node21Context active.node18).G.object.input.vertices.card :=
  (Nat.pow_le_pow_left
    (node151ColdNonCubic_length_le_totalSurplus active) 2).trans
      active.node21.nearCubicBudget

abbrev Node151Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun _residual active _failed =>
      { loss : Nat //
        loss = (node151ColdNonCubicWindows active).length ∧
        loss ^ 2 ≤ node19SurplusCoefficient *
          (Node21Context active.node18).G.object.input.vertices.card ∧
        ∃ cubicCount,
          cubicCount = (node151ColdCubicWindows active).length ∧
          cubicCount + loss = node150ColdCount active })
    residual

noncomputable def node151AmbientCubicColdRefinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node150Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node151Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Output := fun residual active failed =>
      Node150ColdResidual (residual := residual) active
        (Node148To150.mk failed active.output.crossMultiplied
          (node148_totalDemand_eq_hot_add_cold active)))
    (Next := fun residual active failed =>
      { loss : Nat //
        loss = (node151ColdNonCubicWindows active).length ∧
        loss ^ 2 ≤ node19SurplusCoefficient *
          (Node21Context active.node18).G.object.input.vertices.card ∧
        ∃ cubicCount,
          cubicCount = (node151ColdCubicWindows active).length ∧
          cubicCount + loss = node150ColdCount active })
    fun _residual active _failed _node150 => by
      refine
        ⟨(node151ColdNonCubicWindows active).length, rfl, ?_, ?_⟩
      · exact node151ColdNonCubic_length_sq_le_nearCubicBudget active
      · exact ⟨(node151ColdCubicWindows active).length, rfl,
          node151Cold_cubic_nonCubic_length active⟩

noncomputable def runInitialThroughNode151 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode150 residual).mapYesStage
    node151AmbientCubicColdRefinement

def node151LocalChecks : Nat := 0

theorem node151LocalChecks_eq_zero : node151LocalChecks = 0 := rfl

end Erdos64EG.Internal
