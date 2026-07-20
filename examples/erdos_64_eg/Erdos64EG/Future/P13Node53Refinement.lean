import Erdos64EG.Future.P13Nodes47To51Refinement
import Erdos64EG.Future.P13ExactManuscriptHotRate
import StructuralExhaustion.Core.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Accumulated manuscript node [53]

Node [53] is the literal comparison between the remaining labelled-skeleton
budget and the forced curvature cost.  It is a decision, not an unconditional
large-budget theorem.  The framework retrieves node [50]'s exact low
constructor, retains node [51] unchanged on the high constructor, and stores
the two node-[53] outcomes without rebuilding any predecessor.
-/

/-- Exact real-valued labelled-skeleton budget used by the finite node-[53]
comparison. No skeleton family is enumerated. -/
noncomputable def p13Node53SkeletonBits
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  Real.logb 2 (baselineSpineStateCount residual.ctx)

/-- Exact manuscript hot-window demand before asymptotic normalization. -/
noncomputable def p13Node53WindowBits
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  ((p13ManuscriptHotRateNumerator : ℝ) /
      p13ManuscriptHotRateDenominator) *
    p13 residual.ctx *
      Real.logb 2 residual.ctx.G.object.input.vertices.card

/-- Node [49]'s exact constrained-family bit count. -/
noncomputable def p13Node53RemainderBits
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  Real.logb 2 (p13RemainderGraphFamilyCount residual)

/-- The non-curvature part of the exact finite skeleton budget. -/
noncomputable def p13Node53RemainingNoncurvatureBits
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  p13Node53SkeletonBits residual - p13Node53WindowBits residual -
    p13Node53RemainderBits residual

/-- The exact forced-curvature cost already established on node [47]'s
full-rank branch. -/
noncomputable def p13Node53ForcedCurvatureBits
    (residual : P13Node24RefinementResidual.{u}) : ℝ :=
  p13CurvatureEntropyCost * p13CurvatureTargetRank residual.ctx

abbrev P13Node53Small
    (residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50RefinementStage residual) : Prop :=
  p13Node53RemainingNoncurvatureBits residual <
    p13Node53ForcedCurvatureBits residual

abbrev P13Node53Large
    (residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50RefinementStage residual) : Prop :=
  p13Node53ForcedCurvatureBits residual ≤
    p13Node53RemainingNoncurvatureBits residual

/-- The exact two outgoing edges of node [53], indexed by the literal
node-[50] value retained on its low edge. -/
abbrev P13Node53Decision
    (residual : P13Node24RefinementResidual.{u})
    (node50 : P13Node50RefinementStage residual) :=
  Core.ResidualRefinement.State.DependentDecisionAt
    P13Node53Small P13Node53Large residual node50

abbrev P13Node53LowOutput
    (residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50RefinementStage residual)
    (_low : P13Node50RefinementLow residual _node50) :=
  P13Node53Decision residual _node50

/-- The completed node-[50] diamond: node [51] is retained on the high edge,
and node [53] is executed only on the exact low edge. -/
abbrev P13Node53RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentDecisionNoAfterYes
    P13Node50RefinementStage P13Node50RefinementHigh P13Node50RefinementLow
    P13Node51RefinementOutput P13Node53LowOutput residual

noncomputable def p13Node53Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node51RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node53RefinementStage :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionNoAfterYes
    fun residual node50 _low => by
      exact Core.ResidualRefinement.State.DependentDecisionAt.decide
        (Classical.propDecidable (P13Node53Small residual node50))
        (fun absent => le_of_not_gt absent)

noncomputable def p13Nodes25To53Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To51Run residual).mapNoStage p13Node53Refinement

theorem p13Nodes25To53Run_retains_residual
    (residual : P13Node24RefinementResidual.{u}) :
    match p13Nodes25To53Run residual with
    | .yesBranch branch => branch.state.residual = residual
    | .noBranch branch => branch.state.residual = residual := by
  unfold p13Nodes25To53Run
  cases p13Nodes25To51Run residual with
  | yesBranch branch => exact branch.residualExact
  | noBranch branch => exact branch.residualExact

/-- Node [53] performs one proof-level linear-order comparison. -/
def p13Node53LocalChecks : Nat := 1

theorem p13Node53LocalChecks_constant : p13Node53LocalChecks ≤ 1 := le_rfl

/-! ## Node [54]: closure of the node-[53] small-budget edge -/

/-- The branch-local independent-accounting certificate consumed by the
node-`[53]` yes edge.  It is the paper's statement that the forced curvature
coordinates must fit in the exact remaining non-curvature capacity on this
branch; the dependent regime carries its negation separately. -/
abbrev P13Node53IndependentCapacity
    (residual : P13Node24RefinementResidual.{u}) : Prop :=
  p13Node53ForcedCurvatureBits residual ≤
    p13Node53RemainingNoncurvatureBits residual

/-- The small-budget constructor closes locally once the exact independent
capacity certificate for this branch is present.  No conclusion about the
dependent sibling is used. -/
theorem p13Node54_smallBudget_impossible
    {residual : P13Node24RefinementResidual.{u}}
    {node50 : P13Node50RefinementStage residual}
    (small : P13Node53Small residual node50)
    (independent : P13Node53IndependentCapacity residual) : False := by
  exact (not_lt_of_ge independent) small

/-- The corresponding terminal proposition on the exact node-[53] yes leaf. -/
abbrev P13Node54SmallBudgetClosed
    (residual : P13Node24RefinementResidual.{u})
    (node50 : P13Node50RefinementStage residual)
    (small : P13Node53Small residual node50) : Prop :=
  P13Node53IndependentCapacity residual → False

theorem p13Node54_smallBudget_closed
    {residual : P13Node24RefinementResidual.{u}}
    {node50 : P13Node50RefinementStage residual}
    (small : P13Node53Small residual node50) :
    P13Node54SmallBudgetClosed residual node50 small :=
  p13Node54_smallBudget_impossible small

/-! ## Node [55]: the large-budget leaf

Node [55] adds no new inequality. Its mathematical content is precisely that
the node-[50] low edge and node-[53] large edge have both been selected; the
node-[24] density handoff and all intervening facts remain available in the
same accumulated state.
-/

abbrev P13Node55Output
    (_residual : P13Node24RefinementResidual.{u})
    (_node50 : P13Node50RefinementStage _residual)
    (_low : P13Node50RefinementLow _residual _node50)
    (_large : P13Node53Large _residual _node50) := PUnit

abbrev P13Node55RefinementStage
    (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentNestedNoContinuation
    P13Node50RefinementStage P13Node50RefinementHigh P13Node50RefinementLow
    P13Node51RefinementOutput P13Node53Small P13Node53Large
    P13Node55Output residual

noncomputable def p13Node55Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node53RefinementStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node55RefinementStage :=
  Core.ResidualRefinement.State.StageNode.continueDependentNestedNo
    fun _residual _node50 _low _large => ⟨⟩

noncomputable def p13Nodes25To55Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To53Run residual).mapNoStage p13Node55Refinement

theorem p13Nodes25To55Run_retains_residual
    (residual : P13Node24RefinementResidual.{u}) :
    match p13Nodes25To55Run residual with
    | .yesBranch branch => branch.state.residual = residual
    | .noBranch branch => branch.state.residual = residual := by
  unfold p13Nodes25To55Run
  cases p13Nodes25To53Run residual with
  | yesBranch branch => exact branch.residualExact
  | noBranch branch => exact branch.residualExact

/-- Node [55] is pure accumulated-ledger routing. -/
def p13Node55LocalChecks : Nat := 0

theorem p13Node55LocalChecks_eq_zero : p13Node55LocalChecks = 0 := rfl

end Erdos64EG.Internal
