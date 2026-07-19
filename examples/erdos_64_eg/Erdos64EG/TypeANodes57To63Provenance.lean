import Erdos64EG.P13Node56Refinement
import Erdos64EG.TypeANode63Support
import StructuralExhaustion.Core.ResidualRefinement

namespace Erdos64EG.Internal.TypeANodes57To63Provenance

open StructuralExhaustion

universe u

/-!
# Nodes [57]--[62] on the accumulated Part-IV ledger

Node `[57]` is the eventual strict-quarter specialization of node `[56]`'s
finite error-bearing cap.  Nodes `[58]`--`[60]` introduce and inspect the
literal integer net charge.  Node `[61]` invokes the existing CT11 negative
budget profile on the canonical connected-component schedule, and node `[62]`
performs the manuscript's high-surplus split on that exact localized support.
-/

/-- The sole new mathematical fact at node `[57]`. -/
structure P13Node57Output (residual : P13Node24RefinementResidual.{u}) where
  strictQuarter :
    4 * p13NetDeficiencyNumerator residual.ctx <
      (p13RemainderVertices residual.ctx).card

/-- Convert the normalized strict inequality to the denominator-free finite
form consumed by the component ledger. -/
theorem strictQuarterNat_of_normalized
    (residual : P13Node24RefinementResidual.{u})
    (remainderPositive : 0 < (p13RemainderVertices residual.ctx).card)
    (strict :
      (p13NetDeficiencyNumerator residual.ctx : ℝ) /
          (p13RemainderVertices residual.ctx).card < 1 / 4) :
    4 * p13NetDeficiencyNumerator residual.ctx <
      (p13RemainderVertices residual.ctx).card := by
  have denominatorPositive :
      (0 : ℝ) < (p13RemainderVertices residual.ctx).card := by
    exact_mod_cast remainderPositive
  rw [div_lt_iff₀ denominatorPositive] at strict
  have scaled :
      (4 * p13NetDeficiencyNumerator residual.ctx : ℝ) <
        (p13RemainderVertices residual.ctx).card := by
    nlinarith
  exact_mod_cast scaled

/-- The manuscript's node-[57] handoff is available on the same eventual tail
as node `[56]`; no finite error term is discarded. -/
theorem node57_eventually
    {ι : Type*} {l : Filter ι}
    (windowSize remainderSize primitiveSize : Nat)
    (residual : ι → P13Node24RefinementResidual.{u})
    (node56 : ∀ i, P13Node56Output (residual i))
    (orderTop : Filter.Tendsto
      (fun i => (residual i).ctx.G.object.input.vertices.card)
      l Filter.atTop)
    (windowFixed : ∀ i,
      (residual i).node21.previous.windowSize = windowSize)
    (remainderFixed : ∀ i,
      (residual i).node21.previous.remainderSize = remainderSize)
    (primitiveFixed : ∀ i,
      (residual i).node21.previous.primitiveSize = primitiveSize) :
    ∀ᶠ i in l, Nonempty (P13Node57Output (residual i)) := by
  have strict := p13Node56_strictQuarter_eventually
    windowSize remainderSize primitiveSize residual node56 orderTop
    windowFixed remainderFixed primitiveFixed
  have remainderLarge :=
    p13Node48_remainder_quarter_density_eventually residual orderTop
  filter_upwards [strict, remainderLarge] with i strictI remainderLargeI
  have orderPositive :
      (0 : ℝ) < (residual i).ctx.G.object.input.vertices.card := by
    exact_mod_cast (show 0 <
        (residual i).ctx.G.object.input.vertices.card by
      have := (residual i).node25.thirteen_le_order
      omega)
  have remainderPositiveReal :
      (0 : ℝ) < (p13RemainderVertices (residual i).ctx).card := by
    nlinarith
  have remainderPositive :
      0 < (p13RemainderVertices (residual i).ctx).card := by
    exact_mod_cast remainderPositiveReal
  exact ⟨{
    strictQuarter := strictQuarterNat_of_normalized
      (residual i) remainderPositive strictI }⟩

/-- Framework-owned attachment of node `[57]` to a branch ledger containing
the literal node-[56] output.  The producer must use that retrieved output. -/
noncomputable def node57Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node56Output) facts]
    (produce : ∀ residual, P13Node56Output residual → P13Node57Output residual) :
    Core.ResidualRefinement.State.StageNode (facts := facts) P13Node57Output :=
  Core.ResidualRefinement.State.StageNode.derive
    (Core.ResidualRefinement.State.LedgerQuery.stage
      (facts := facts) (Stage := P13Node56Output))
    fun state node56 => produce state.residual node56

/-- Node `[58]`: the exact quarter-scaled integer net charge. -/
structure P13Node58Output (residual : P13Node24RefinementResidual.{u}) where
  netQuarter : Int
  netQuarterExact : netQuarter =
    4 * (p13NetDeficiencyNumerator residual.ctx : Int) -
      ((p13RemainderVertices residual.ctx).card : Int)

noncomputable def node58Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node57Output) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) P13Node58Output :=
  Core.ResidualRefinement.State.StageNode.derive
    (Core.ResidualRefinement.State.LedgerQuery.stage
      (facts := facts) (Stage := P13Node57Output))
    fun state _node57 => {
      netQuarter := 4 * (p13NetDeficiencyNumerator state.residual.ctx : Int) -
        ((p13RemainderVertices state.residual.ctx).card : Int)
      netQuarterExact := rfl }

/-- Node `[59]`'s surviving no edge, on the same integer charge. -/
structure P13Node59NegativeOutput (residual : P13Node24RefinementResidual.{u}) where
  negative :
    4 * (p13NetDeficiencyNumerator residual.ctx : Int) -
      ((p13RemainderVertices residual.ctx).card : Int) < 0

noncomputable def node59Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node57Output) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node58Output) facts] :
    Core.ResidualRefinement.State.StageNode
      (facts := facts) P13Node59NegativeOutput :=
  Core.ResidualRefinement.State.StageNode.derive
    ((Core.ResidualRefinement.State.LedgerQuery.stage
      (facts := facts) (Stage := P13Node57Output)).andStage
        (Stage := P13Node58Output))
    fun state inputs => {
      negative := by
        have strictInt :
            (4 * p13NetDeficiencyNumerator state.residual.ctx : Int) <
              ((p13RemainderVertices state.residual.ctx).card : Int) := by
          exact_mod_cast inputs.fst.strictQuarter
        omega }

/-- Node `[60]`: the yes edge of node `[59]` contradicts the retained strict
negative charge. -/
theorem node60_impossible
    {residual : P13Node24RefinementResidual.{u}}
    (node58 : P13Node58Output residual)
    (node59 : P13Node59NegativeOutput residual)
    (nonnegative : 0 ≤ node58.netQuarter) : False := by
  rw [node58.netQuarterExact] at nonnegative
  exact (Int.not_lt_of_ge nonnegative) node59.negative

/-- Node `[61]` adds only CT11's localized support to the accumulated ledger. -/
abbrev P13Node61Output (residual : P13Node24RefinementResidual.{u}) :=
  TypeBEntryRouting.VerifiedNode61Residual residual.ctx

noncomputable def node61Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node57Output) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node59NegativeOutput) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) P13Node61Output :=
  Core.ResidualRefinement.State.StageNode.derive
    ((Core.ResidualRefinement.State.LedgerQuery.stage
      (facts := facts) (Stage := P13Node57Output)).andStage
        (Stage := P13Node59NegativeOutput))
    fun state inputs =>
      P13NegativeSupportLocalization.canonicalNode61 state.residual.ctx {
        node21 := state.residual.node21
        strictQuarter := inputs.fst.strictQuarter }

/-- Node `[62]` uses the already graph-owned exhaustive high-center split. -/
noncomputable def node62
    {residual : P13Node24RefinementResidual.{u}}
    (node61 : P13Node61Output residual) :
    TypeANode63Support.VerifiedNode62Routed node61 :=
  TypeANode63Support.routeNode62 node61

/-- CT11 scans the canonical component list once; node `[62]` scans the
selected support once. -/
noncomputable def localChecks
    {residual : P13Node24RefinementResidual.{u}}
    (node61 : P13Node61Output residual) : Nat :=
  (P13NegativeSupportLocalization.Canonical.cells residual.ctx).values.length +
    node61.support.core.card

theorem localChecks_linear
    {residual : P13Node24RefinementResidual.{u}}
    (node61 : P13Node61Output residual) :
    localChecks node61 ≤ 2 * residual.ctx.G.object.input.vertices.card := by
  have cells :=
    P13NegativeSupportLocalization.Canonical.scan_linear residual.ctx
  have support : node61.support.core.card ≤
      residual.ctx.G.object.input.vertices.card := by
    rw [← residual.ctx.G.object.card_vertexFinset]
    exact Finset.card_le_card fun vertex _ =>
      residual.ctx.G.object.mem_vertexFinset vertex
  unfold localChecks
  omega

end Erdos64EG.Internal.TypeANodes57To63Provenance
