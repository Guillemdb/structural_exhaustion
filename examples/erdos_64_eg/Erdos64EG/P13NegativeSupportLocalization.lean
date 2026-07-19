import Erdos64EG.TypeBEntryRouting
import Erdos64EG.P13LargeBudgetNetDeficiency
import StructuralExhaustion.CT11.NegativeBudget
import StructuralExhaustion.Graph.OrderedSupportComponents

namespace Erdos64EG.Internal.P13NegativeSupportLocalization

open StructuralExhaustion

universe u

variable
  (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})

/-- One actual connected cell of the canonical remainder decomposition.  It
does not carry a negativity hypothesis: CT11 must discover that locally. -/
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
  cell.chargeProfile ctx |>.netQuarterCharge

end SupportCell

namespace Canonical

abbrev RemainderComponent :=
  Graph.OrderedSupportComponents.Component ctx.G.object
    (p13RemainderVertices ctx)

abbrev ComponentIndex :=
  {component : RemainderComponent ctx // component ∈
    Graph.OrderedSupportComponents.order ctx.G.object
      (p13RemainderVertices ctx)}

/-- Exact first-occurrence order of the actual remainder components. -/
noncomputable def componentIndices :
    Core.OrderedCollection (ComponentIndex ctx) where
  values := (Graph.OrderedSupportComponents.order ctx.G.object
    (p13RemainderVertices ctx)).attach
  nodup := by
    simpa using (Graph.OrderedSupportComponents.order_nodup ctx.G.object
      (p13RemainderVertices ctx)).attach
  decEq := Classical.decEq _

/-- Convert one graph-owned component to the exact CT11 support cell. -/
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

/-- Pointwise quarter charge on the exact remainder. -/
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

/-- The one canonical ordered CT11 cell schedule; no component family is a
caller field. -/
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
  · rintro ⟨supportCell, cellMember, vertexMember⟩
    exact supportCell.core_subset_remainder vertexMember
  · intro remainderMember
    obtain ⟨supportCell, cellMember, vertexMember⟩ :=
      covers ctx vertex remainderMember
    exact ⟨supportCell,
      (Core.OrderedCollection.mem_toFinset (cells ctx) supportCell).mpr cellMember,
      vertexMember⟩

/-- Exact component additivity for the literal pointwise remainder charge. -/
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
          remainderPointCharge ctx vertex :=
      by
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

/-- Natural subtraction in the upstream finite budget can only overestimate
the true integer charge when surplus exceeds deficiency. -/
theorem sum_localBudget_le_netNumerator :
    ((cells ctx).values.map (SupportCell.localBudget ctx)).sum ≤
      4 * (p13NetDeficiencyNumerator ctx : Int) -
        ((p13RemainderVertices ctx).card : Int) := by
  rw [sum_localBudget_eq_pointCharge ctx, sum_pointCharge_eq ctx]
  unfold p13NetDeficiencyNumerator
  rw [p13Curvature_positiveDeficiency_eq_previous]
  have truncation :
      ((p13RemainderCurvatureProfile ctx).positiveDeficiency : Int) -
          (Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object : Int) ≤
        ((p13RemainderCurvatureProfile ctx).positiveDeficiency -
          Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object : Nat) := by
    omega
  omega

end Canonical

/-- Exact predecessor package for node `[61]`: one proved duplicate-free
ordered decomposition, its same-context sparse-surplus ancestry, literal
remainder coverage, and the negative total ledger.  No family of alternative
decompositions is enumerated. -/
structure Decomposition where
  previous : VerifiedSparseSurplusPrefix ctx
  cells : Core.OrderedCollection (SupportCell ctx)
  covers : ∀ vertex ∈ p13RemainderVertices ctx,
    ∃ cell ∈ cells.values, vertex ∈ cell.core
  pairwise_disjoint : cells.values.Pairwise fun left right =>
    Disjoint left.core right.core
  scan_linear : cells.values.length ≤ ctx.G.object.input.vertices.card
  negativeTotal :
    (cells.values.map (SupportCell.localBudget ctx)).sum < 0

/-- Build node `[61]`'s CT11 input from the graph-owned canonical component
schedule and a proved negative total. -/
noncomputable def canonicalDecomposition
    (previous : VerifiedSparseSurplusPrefix ctx)
    (negativeTotal :
      ((Canonical.cells ctx).values.map
        (SupportCell.localBudget ctx)).sum < 0) : Decomposition ctx where
  previous := previous
  cells := Canonical.cells ctx
  covers := Canonical.covers ctx
  pairwise_disjoint := Canonical.pairwise_disjoint ctx
  scan_linear := Canonical.scan_linear ctx
  negativeTotal := negativeTotal

/-- Exact additive component ledger expected between the strict-quarter
remainder budget and CT11.  The cells are the one canonical decomposition;
`chargeUpper` is derived from graph-theoretic component additivity and the
upstream natural-subtraction budget, not from a selected negative-cell
certificate. -/
structure QuarterDecomposition where
  node21 : VerifiedP13MultiScaleCurvaturePrefix ctx
  strictQuarter :
    4 * p13NetDeficiencyNumerator ctx < (p13RemainderVertices ctx).card
  previous : VerifiedSparseSurplusPrefix ctx
  cells : Core.OrderedCollection (SupportCell ctx)
  covers : ∀ vertex ∈ p13RemainderVertices ctx,
    ∃ cell ∈ cells.values, vertex ∈ cell.core
  pairwise_disjoint : cells.values.Pairwise fun left right =>
    Disjoint left.core right.core
  scan_linear : cells.values.length ≤ ctx.G.object.input.vertices.card
  chargeUpper :
    (cells.values.map (SupportCell.localBudget ctx)).sum ≤
      4 * (p13NetDeficiencyNumerator ctx : Int) -
        ((p13RemainderVertices ctx).card : Int)

/-- Same-context inputs needed to connect the genuine node-`[24]`
strict-quarter output to the graph-owned canonical component schedule. -/
structure CanonicalQuarterLedger where
  node21 : VerifiedP13MultiScaleCurvaturePrefix ctx
  strictQuarter :
    4 * p13NetDeficiencyNumerator ctx < (p13RemainderVertices ctx).card

noncomputable def CanonicalQuarterLedger.toQuarterDecomposition
    (ledger : CanonicalQuarterLedger ctx) : QuarterDecomposition ctx where
  node21 := ledger.node21
  strictQuarter := ledger.strictQuarter
  previous := verifiedSparseSurplusPrefix ctx
    ledger.node21.previous.previous.residual
  cells := Canonical.cells ctx
  covers := Canonical.covers ctx
  pairwise_disjoint := Canonical.pairwise_disjoint ctx
  scan_linear := Canonical.scan_linear ctx
  chargeUpper := Canonical.sum_localBudget_le_netNumerator ctx

theorem QuarterDecomposition.negativeTotal
    (decomposition : QuarterDecomposition ctx) :
    (decomposition.cells.values.map (SupportCell.localBudget ctx)).sum < 0 := by
  have strictQuarterInt :
      4 * (p13NetDeficiencyNumerator ctx : Int) <
        ((p13RemainderVertices ctx).card : Int) := by
    exact_mod_cast decomposition.strictQuarter
  exact decomposition.chargeUpper.trans_lt (by omega)

/-- The strict-quarter handoff and exact additive ledger provide CT11's
negative-total input without choosing a component in advance. -/
def QuarterDecomposition.toDecomposition
    (decomposition : QuarterDecomposition ctx) : Decomposition ctx where
  previous := decomposition.previous
  cells := decomposition.cells
  covers := decomposition.covers
  pairwise_disjoint := decomposition.pairwise_disjoint
  scan_linear := decomposition.scan_linear
  negativeTotal := decomposition.negativeTotal

/-- CT11 specializes to the literal component charge used by the manuscript. -/
noncomputable def profile : CT11.NegativeBudgetProfile PackedProblem where
  Cell := SupportCell ctx
  localBudget := fun _context cell => cell.localBudget ctx

noncomputable def run (decomposition : Decomposition ctx) :=
  (profile ctx).run ctx.toBranchContext decomposition.cells
    decomposition.negativeTotal

theorem run_terminal_localized (decomposition : Decomposition ctx) :
    (run ctx decomposition).terminal = .localized :=
  (profile ctx).run_terminal_localized ctx.toBranchContext decomposition.cells
    decomposition.negativeTotal

noncomputable def localizedResidual (decomposition : Decomposition ctx) :=
  (profile ctx).residual ctx.toBranchContext decomposition.cells
    decomposition.negativeTotal

theorem localized_cell_mem (decomposition : Decomposition ctx) :
    (localizedResidual ctx decomposition).cell ∈ decomposition.cells.values :=
  (localizedResidual ctx decomposition).member

theorem localized_cell_negative (decomposition : Decomposition ctx) :
    ((localizedResidual ctx decomposition).cell.chargeProfile ctx).netQuarterCharge < 0 :=
  (localizedResidual ctx decomposition).negative

/-- Node `[61]` is now produced by CT11 from the negative component sum; the
negative component is not supplied or guessed by the caller. -/
noncomputable def node61 (decomposition : Decomposition ctx) :
    TypeBEntryRouting.VerifiedNode61Residual ctx := by
  let cell := (localizedResidual ctx decomposition).cell
  let support : TypeBEntryRouting.NegativeSupport ctx := {
    core := cell.core
    connected := cell.connected
    negative := localized_cell_negative ctx decomposition }
  exact TypeBEntryRouting.node61 ctx decomposition.previous support
    cell.core_subset_remainder cell.remainder_neighbor_closed

@[simp]
theorem node61_core (decomposition : Decomposition ctx) :
    (node61 ctx decomposition).support.core =
      (localizedResidual ctx decomposition).cell.core :=
  rfl

theorem node61_negative (decomposition : Decomposition ctx) :
    (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
      (node61 ctx decomposition).support.core).netQuarterCharge < 0 :=
  (node61 ctx decomposition).support.negative

/-- Complete canonical node-`[61]` producer from the genuine strict-quarter
handoff: component construction, charge additivity, CT11 localization, and
same-context sparse-surplus ancestry are all derived. -/
noncomputable def canonicalNode61 (ledger : CanonicalQuarterLedger ctx) :
    TypeBEntryRouting.VerifiedNode61Residual ctx :=
  node61 ctx (ledger.toQuarterDecomposition.toDecomposition)

theorem localization_checks_linear (decomposition : Decomposition ctx) :
    decomposition.cells.values.length ≤ ctx.G.object.input.vertices.card :=
  decomposition.scan_linear

end Erdos64EG.Internal.P13NegativeSupportLocalization
