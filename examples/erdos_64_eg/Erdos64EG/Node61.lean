import Erdos64EG.Node60
import StructuralExhaustion.CT11.NegativeBudget
import StructuralExhaustion.Graph.OrderedSupportComponents
import StructuralExhaustion.Routes.NegativeSupportHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-- Problem-64 Part-V ambient baseline degree. -/
def node62P13BaselineDegree : Nat := 3

/-- Problem-64 Part-V high-surplus threshold, expressed through the
baseline rather than as an independent framework constant. -/
def node62P13HighThreshold : Nat := node62P13BaselineDegree + 1

theorem node62P13HighThreshold_eq :
    node62P13HighThreshold = node62P13BaselineDegree + 1 := rfl

/-- Problem-64 Part-V signed charge parameters. -/
def node62P13ChargeParameters :
    Graph.AssignedSupportCharge.Parameters where
  baseline := node62P13BaselineDegree
  scale := 4

theorem node61P13ChargeProfileWith_netCharge_eq {V : Type u}
    (object : Graph.FiniteObject V) (core : Finset V) :
    (Graph.NegativeSupportHandoff.chargeProfileWith
      object node62P13ChargeParameters
      node62P13HighThreshold core).netCharge =
      (Graph.NegativeSupportHandoff.chargeProfile
        object core).netQuarterCharge := by
  rfl

/-!
# Diagram node [61]: connected negative net-charge support

Node [61] consumes exactly the node-[60] residual.  Closed/bypass leaves are
transported by Core.  On the literal node-[59] negative leaf, the node runs the
framework CT11 negative-budget localizer on the canonical connected-component
schedule of the already selected `P₁₃` remainder.  The application supplies
only the P13 remainder charge identities needed to instantiate CT11.
-/

namespace Node61Localization

variable
  (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})

/-- One actual connected cell of the canonical remainder decomposition. -/
structure SupportCell where
  core : Finset ctx.G.Vertex
  connected : Graph.NegativeSupportHandoff.ConnectedOn ctx.G.object core
  core_subset_remainder : core ⊆ p13RemainderVertices ctx
  remainder_neighbor_closed : ∀ ⦃vertex neighbor : ctx.G.Vertex⦄,
    vertex ∈ core → neighbor ∈ p13RemainderVertices ctx →
      ctx.G.object.graph.Adj vertex neighbor → neighbor ∈ core

namespace SupportCell

noncomputable def chargeProfile (cell : SupportCell ctx) :
    Graph.AssignedSupportCharge.Profile ctx.G.object :=
  Graph.NegativeSupportHandoff.chargeProfile ctx.G.object cell.core

noncomputable def localBudget (cell : SupportCell ctx) : Int :=
  (cell.chargeProfile ctx).netQuarterCharge

end SupportCell

namespace Canonical

abbrev RemainderComponent :=
  Graph.OrderedSupportComponents.Component ctx.G.object
    (p13RemainderVertices ctx)

abbrev ComponentIndex :=
  {component : RemainderComponent ctx // component ∈
    Graph.OrderedSupportComponents.order ctx.G.object
      (p13RemainderVertices ctx)}

noncomputable def componentIndices :
    Core.OrderedCollection (ComponentIndex ctx) where
  values := (Graph.OrderedSupportComponents.order ctx.G.object
    (p13RemainderVertices ctx)).attach
  nodup := by
    simpa using (Graph.OrderedSupportComponents.order_nodup ctx.G.object
      (p13RemainderVertices ctx)).attach
  decEq := Classical.decEq _

noncomputable def cell (index : ComponentIndex ctx) : SupportCell ctx where
  core := Graph.OrderedSupportComponents.vertices ctx.G.object
    (p13RemainderVertices ctx) index.1
  connected := Graph.OrderedSupportComponents.connectedOn_of_mem_order
    ctx.G.object (p13RemainderVertices ctx) index.2
  core_subset_remainder := by
    intro vertex member
    exact (Graph.OrderedSupportComponents.mem_support_iff_mem_component
      ctx.G.object (p13RemainderVertices ctx) vertex).mpr
        ⟨index.1, index.2, member⟩
  remainder_neighbor_closed := by
    intro vertex neighbor vertexMember neighborRemainder adjacent
    exact Graph.OrderedSupportComponents.neighbor_mem_vertices ctx.G.object
      (p13RemainderVertices ctx) index.1 vertexMember neighborRemainder adjacent

theorem cell_internalDegree_eq_remainder (index : ComponentIndex ctx)
    (vertex : ctx.G.Vertex) (member : vertex ∈ (cell ctx index).core) :
    ((cell ctx index).chargeProfile ctx).internalDegree vertex =
      (p13RemainderDeficiencyProfile ctx).internalDegree vertex := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  unfold SupportCell.chargeProfile
  unfold Graph.NegativeSupportHandoff.chargeProfile
  unfold Graph.AssignedSupportCharge.Profile.internalDegree
  apply congrArg Finset.card
  ext neighbor
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨adjacent, neighborMember⟩
    exact ⟨adjacent, (cell ctx index).core_subset_remainder neighborMember⟩
  · rintro ⟨adjacent, neighborRemainder⟩
    have adjacent' : ctx.G.object.graph.Adj vertex neighbor := by
      simpa [SimpleGraph.mem_neighborFinset] using adjacent
    exact ⟨adjacent,
      Graph.OrderedSupportComponents.neighbor_mem_vertices ctx.G.object
        (p13RemainderVertices ctx) index.1 member neighborRemainder adjacent'⟩

noncomputable def remainderPointCharge (vertex : ctx.G.Vertex) : Int :=
  4 * ((p13RemainderDeficiencyProfile ctx).positiveDeficiencyAt vertex : Int) -
    4 * (Graph.AssignedSupportCharge.Profile.surplusAt
      ctx.G.object vertex : Int) - 1

theorem cell_assignedSurplus_eq (index : ComponentIndex ctx) :
    ((cell ctx index).chargeProfile ctx).assignedSurplus =
      ∑ vertex ∈ (cell ctx index).core,
        Graph.AssignedSupportCharge.Profile.surplusAt ctx.G.object vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold SupportCell.chargeProfile Graph.NegativeSupportHandoff.chargeProfile
  unfold Graph.AssignedSupportCharge.Profile.assignedSurplus
  unfold Graph.NegativeSupportHandoff.highCenters
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro vertex coreMember notHighMember
  have notHigh : ¬4 ≤ ctx.G.object.degree vertex := by
    intro high
    apply notHighMember
    exact Finset.mem_filter.mpr ⟨coreMember, high⟩
  have lower : 3 ≤ ctx.G.object.degree vertex :=
    ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex)
  have degree : ctx.G.object.degree vertex = 3 := by omega
  simp [Graph.AssignedSupportCharge.Profile.surplusAt, degree]

theorem cell_localBudget_eq_sum (index : ComponentIndex ctx) :
    (cell ctx index).localBudget ctx =
      ∑ vertex ∈ (cell ctx index).core, remainderPointCharge ctx vertex := by
  classical
  unfold SupportCell.localBudget remainderPointCharge
  unfold Graph.AssignedSupportCharge.Profile.netQuarterCharge
  unfold Graph.AssignedSupportCharge.Profile.positiveDeficiency
  simp only [SupportCell.chargeProfile,
    Graph.NegativeSupportHandoff.chargeProfile] at *
  have surplusEq := cell_assignedSurplus_eq ctx index
  simp only [SupportCell.chargeProfile,
    Graph.NegativeSupportHandoff.chargeProfile] at surplusEq
  rw [surplusEq]
  have deficiencyPointwise : ∀ vertex ∈ (cell ctx index).core,
      ((cell ctx index).chargeProfile ctx).positiveDeficiencyAt vertex =
        (p13RemainderDeficiencyProfile ctx).positiveDeficiencyAt vertex := by
    intro vertex member
    unfold Graph.AssignedSupportCharge.Profile.positiveDeficiencyAt
    rw [cell_internalDegree_eq_remainder ctx index vertex member]
  have deficiencySum :
      (∑ vertex ∈ (cell ctx index).core,
        ({ core := (cell ctx index).core
           assignedCenters := Graph.NegativeSupportHandoff.highCenters
             ctx.G.object (cell ctx index).core } :
          Graph.AssignedSupportCharge.Profile ctx.G.object).positiveDeficiencyAt
            vertex) =
        ∑ vertex ∈ (cell ctx index).core,
          (p13RemainderDeficiencyProfile ctx).positiveDeficiencyAt vertex := by
    apply Finset.sum_congr rfl
    intro vertex member
    simpa only [SupportCell.chargeProfile,
      Graph.NegativeSupportHandoff.chargeProfile] using
        deficiencyPointwise vertex member
  rw [deficiencySum]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp

theorem cell_injective : Function.Injective (cell ctx) := by
  intro left right equal
  apply Subtype.ext
  by_contra different
  have disjoint := Graph.OrderedSupportComponents.disjoint_vertices
    ctx.G.object (p13RemainderVertices ctx) different
  have nonempty := Graph.OrderedSupportComponents.vertices_nonempty_of_mem_order
    ctx.G.object (p13RemainderVertices ctx) left.2
  obtain ⟨vertex, leftMember⟩ := nonempty
  have coresEqual := congrArg SupportCell.core equal
  change Graph.OrderedSupportComponents.vertices ctx.G.object
      (p13RemainderVertices ctx) left.1 =
    Graph.OrderedSupportComponents.vertices ctx.G.object
      (p13RemainderVertices ctx) right.1 at coresEqual
  have rightMember : vertex ∈ Graph.OrderedSupportComponents.vertices
      ctx.G.object (p13RemainderVertices ctx) right.1 := by
    rw [← coresEqual]
    exact leftMember
  exact (Finset.disjoint_left.mp disjoint) leftMember rightMember

noncomputable def cells : Core.OrderedCollection (SupportCell ctx) where
  values := (componentIndices ctx).values.map (cell ctx)
  nodup := (componentIndices ctx).nodup.map (cell_injective ctx)
  decEq := Classical.decEq _

theorem covers (vertex : ctx.G.Vertex)
    (member : vertex ∈ p13RemainderVertices ctx) :
    ∃ supportCell ∈ (cells ctx).values, vertex ∈ supportCell.core := by
  obtain ⟨component, componentMember, vertexMember⟩ :=
    (Graph.OrderedSupportComponents.mem_support_iff_mem_component
      ctx.G.object (p13RemainderVertices ctx) vertex).mp member
  let index : ComponentIndex ctx := ⟨component, componentMember⟩
  refine ⟨cell ctx index, ?_, vertexMember⟩
  unfold cells
  apply List.mem_map.mpr
  exact ⟨index, by simp [componentIndices, index], rfl⟩

theorem pairwise_disjoint :
    (cells ctx).values.Pairwise fun left right =>
      Disjoint left.core right.core := by
  unfold cells
  rw [List.pairwise_map]
  apply (List.nodup_iff_pairwise_ne.mp (componentIndices ctx).nodup).imp
  intro left right different
  exact Graph.OrderedSupportComponents.disjoint_vertices ctx.G.object
    (p13RemainderVertices ctx) (by
      intro equal
      exact different (Subtype.ext equal))

theorem scan_linear :
    (cells ctx).values.length ≤ ctx.G.object.input.vertices.card := by
  have componentBound :=
    Graph.OrderedSupportComponents.order_length_le_support_card
      ctx.G.object (p13RemainderVertices ctx)
  have remainderBound : (p13RemainderVertices ctx).card ≤
      ctx.G.object.input.vertices.card := by
    rw [← ctx.G.object.card_vertexFinset]
    apply Finset.card_le_card
    intro vertex _member
    exact ctx.G.object.mem_vertexFinset vertex
  simpa [cells, componentIndices] using componentBound.trans remainderBound

theorem cellFinset_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (↑(cells ctx).toFinset : Set (SupportCell ctx))
      (fun supportCell : SupportCell ctx => supportCell.core) := by
  classical
  intro left leftMember right rightMember different
  change left ∈ (cells ctx).toFinset at leftMember
  change right ∈ (cells ctx).toFinset at rightMember
  rw [Core.OrderedCollection.mem_toFinset] at leftMember rightMember
  unfold cells at leftMember rightMember
  obtain ⟨leftIndex, _leftIndexMember, rfl⟩ := List.mem_map.mp leftMember
  obtain ⟨rightIndex, _rightIndexMember, rfl⟩ := List.mem_map.mp rightMember
  apply Graph.OrderedSupportComponents.disjoint_vertices ctx.G.object
    (p13RemainderVertices ctx)
  intro componentEqual
  apply different
  have indexEqual : leftIndex = rightIndex := Subtype.ext componentEqual
  rw [indexEqual]

noncomputable def unionCores : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (cells ctx).toFinset.biUnion (fun supportCell => supportCell.core)

theorem unionCores_eq_remainder :
    unionCores ctx = p13RemainderVertices ctx := by
  classical
  unfold unionCores
  ext vertex
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨supportCell, _cellMember, vertexMember⟩
    exact supportCell.core_subset_remainder vertexMember
  · intro remainderMember
    obtain ⟨supportCell, cellMember, vertexMember⟩ :=
      covers ctx vertex remainderMember
    exact ⟨supportCell,
      (Core.OrderedCollection.mem_toFinset (cells ctx) supportCell).mpr
        cellMember,
      vertexMember⟩

theorem sum_localBudget_eq_pointCharge :
    ((cells ctx).values.map (SupportCell.localBudget ctx)).sum =
      ∑ vertex ∈ p13RemainderVertices ctx,
        remainderPointCharge ctx vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  classical
  rw [Core.OrderedCollection.sum_values_eq_sum_toFinset]
  calc
    ∑ supportCell ∈ (cells ctx).toFinset,
        supportCell.localBudget ctx =
        ∑ supportCell ∈ (cells ctx).toFinset,
          ∑ vertex ∈ supportCell.core,
            remainderPointCharge ctx vertex := by
      apply Finset.sum_congr rfl
      intro supportCell supportCellMember
      rw [Core.OrderedCollection.mem_toFinset] at supportCellMember
      unfold cells at supportCellMember
      obtain ⟨index, _indexMember, equal⟩ := List.mem_map.mp supportCellMember
      subst supportCell
      exact cell_localBudget_eq_sum ctx index
    _ = ∑ vertex ∈ unionCores ctx,
          remainderPointCharge ctx vertex := by
      unfold unionCores
      exact (Finset.sum_biUnion (M := Int)
        (f := remainderPointCharge ctx)
        (cellFinset_pairwiseDisjoint ctx)).symm
    _ = ∑ vertex ∈ p13RemainderVertices ctx,
          remainderPointCharge ctx vertex := by
      rw [unionCores_eq_remainder ctx]

theorem sum_pointCharge_eq :
    (∑ vertex ∈ p13RemainderVertices ctx,
      remainderPointCharge ctx vertex) =
      4 * ((p13RemainderDeficiencyProfile ctx).positiveDeficiency : Int) -
        4 * (Graph.InducedPathWindowLedger.remainderSurplus
          ctx.G.object : Int) -
        ((p13RemainderVertices ctx).card : Int) := by
  classical
  unfold remainderPointCharge
  unfold Graph.AssignedSupportCharge.Profile.positiveDeficiency
  unfold Graph.InducedPathWindowLedger.remainderSurplus
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  push_cast
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp [p13RemainderDeficiencyProfile, p13RemainderVertices,
    Graph.AssignedSupportCharge.Profile.surplusAt]

theorem sum_localBudget_le_netNumerator :
    ((cells ctx).values.map (SupportCell.localBudget ctx)).sum ≤
      4 * (node56RemainderNetDeficiencyNumerator ctx : Int) -
        ((p13RemainderVertices ctx).card : Int) := by
  rw [sum_localBudget_eq_pointCharge ctx, sum_pointCharge_eq ctx]
  unfold node56RemainderNetDeficiencyNumerator
  rw [p13Curvature_positiveDeficiency_eq_previous]
  have truncation :
      ((p13RemainderCurvatureProfile ctx).positiveDeficiency : Int) -
          (Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object : Int) ≤
        ((p13RemainderCurvatureProfile ctx).positiveDeficiency -
          Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object : Nat) := by
    omega
  omega

end Canonical

noncomputable def profile :
    CT11.NegativeBudgetProfile PackedProblem where
  Cell := SupportCell ctx
  localBudget := fun _context cell => cell.localBudget ctx

noncomputable def localizedResidual
    (negativeTotal :
      ((Canonical.cells ctx).values.map
        (SupportCell.localBudget ctx)).sum < 0) :=
  (profile ctx).residual ctx.toBranchContext (Canonical.cells ctx)
    negativeTotal

theorem localized_cell_negative
    (negativeTotal :
      ((Canonical.cells ctx).values.map
        (SupportCell.localBudget ctx)).sum < 0) :
    (((localizedResidual ctx negativeTotal).cell).chargeProfile ctx).netQuarterCharge < 0 :=
  (localizedResidual ctx negativeTotal).negative

theorem negativeTotal_of_strict
    (strict :
      4 * ((node56RemainderNetDeficiencyNumerator ctx : Int)) -
        ((p13RemainderVertices ctx).card : Int) < 0) :
    ((Canonical.cells ctx).values.map
      (SupportCell.localBudget ctx)).sum < 0 := by
  have upper :=
    Canonical.sum_localBudget_le_netNumerator ctx
  exact upper.trans_lt strict

end Node61Localization

abbrev Node61Context {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) :=
  Node21Context active.previous

abbrev Node61ConnectedSupport {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) :=
  Graph.NegativeSupportHandoff.ConnectedNegativeSupportWith
    (Node61Context active).G.object node62P13ChargeParameters
    node62P13HighThreshold

/-- Node [61]'s sole live payload: the connected support selected by CT11. -/
structure Node61Output : Type (u + 2) where
  ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}
  support :
    Graph.NegativeSupportHandoff.ConnectedNegativeSupportWith
      ctx.G.object node62P13ChargeParameters node62P13HighThreshold
  core_subset_remainder :
    support.core ⊆ p13RemainderVertices ctx
  remainder_neighbor_closed : ∀ ⦃vertex neighbor : ctx.G.Vertex⦄,
    vertex ∈ support.core →
      neighbor ∈ p13RemainderVertices ctx →
      ctx.G.object.graph.Adj vertex neighbor →
        neighbor ∈ support.core
  localizationWork :
    (Node61Localization.Canonical.cells
      ctx).values.length ≤
      ctx.G.object.input.vertices.card

/-- Construct node [61] from the exact node-[56] strict net-cap output. -/
noncomputable def node61OutputOfStrict
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (strict :
      4 * ((node56RemainderNetDeficiencyNumerator ctx : Int)) -
        ((p13RemainderVertices ctx).card : Int) < 0) :
    Node61Output.{u} := by
  have negativeTotal :
      ((Node61Localization.Canonical.cells ctx).values.map
        (Node61Localization.SupportCell.localBudget ctx)).sum < 0 :=
    Node61Localization.negativeTotal_of_strict ctx strict
  let localized := Node61Localization.localizedResidual ctx negativeTotal
  let cell := localized.cell
  let support :
      Graph.NegativeSupportHandoff.ConnectedNegativeSupportWith
        ctx.G.object node62P13ChargeParameters node62P13HighThreshold := {
    core := cell.core
    connected := cell.connected
    negative := by
      rw [node61P13ChargeProfileWith_netCharge_eq]
      exact Node61Localization.localized_cell_negative ctx negativeTotal
  }
  exact {
    ctx := ctx
    support := support
    core_subset_remainder := cell.core_subset_remainder
    remainder_neighbor_closed := cell.remainder_neighbor_closed
    localizationWork := Node61Localization.Canonical.scan_linear ctx
  }

/-- Node [61]'s successor payload, indexed by the exact node-[60] predecessor
selected by Core. -/
abbrev Node61Next {V : Type u} {residual : InitialResidual V}
    (node60 : Node60Stage residual) : Type (u + 2) :=
  match node60 with
  | ⟨⟨⟨.bypass _, _node57⟩, _node58⟩, _node60⟩ =>
      PUnit.{u + 3}
  | ⟨⟨⟨.degraded _data _node56, _node57⟩, _node58⟩, _node60⟩ =>
      Node61Output.{u}
  | ⟨⟨⟨.alternate _data _ _node56, _node57⟩, _node58⟩, _node60⟩ =>
      Node61Output.{u}

/-- The complete carrier after node [61]. -/
abbrev Node61Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (@Node60Stage V)
    (fun _residual node60 => Node61Next node60)
    residual

/-- Framework-owned successor `[60] -> [61]`. -/
noncomputable def node61P13NegativeSupport {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node60Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node61Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (Previous := @Node60Stage V)
    (Next := fun _residual node60 => Node61Next node60)
    fun _residual node60 =>
      match node60 with
      | ⟨⟨⟨.bypass _, _node57⟩, _node58⟩, _node60⟩ =>
          (PUnit.unit : PUnit.{u + 3})
      | ⟨⟨⟨.degraded data node56, _node57⟩, _node58⟩, _node60⟩ =>
          node61OutputOfStrict (Node21Context data.data.previous)
            (by
              simpa using node56.remainderNetChargeQuarterNegative)
      | ⟨⟨⟨.alternate data _ node56, _node57⟩, _node58⟩, _node60⟩ =>
          node61OutputOfStrict (Node21Context data.data.previous)
            (by
              simpa using node56.remainderNetChargeQuarterNegative)

noncomputable def runInitialThroughNode61 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode60 residual).mapYesStage
    node61P13NegativeSupport

noncomputable def node61LocalChecks (output : Node61Output.{u}) : Nat :=
  (Node61Localization.Canonical.cells
    output.ctx).values.length

theorem node61LocalChecks_linear (output : Node61Output.{u}) :
    node61LocalChecks output ≤
      output.ctx.G.object.input.vertices.card :=
  output.localizationWork

end Erdos64EG.Internal
