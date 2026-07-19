import Erdos64EG.P13Node146Route8Threshold

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Node [147]: dependency-ready private-carrier collision arithmetic

The original terminal node consumes two ingredients: the yes payload of node
`[146]`, and the already constructed Type-A route-8 private-carrier ledger.
The current node-`[146]` payload contains the former but not the latter.  This
file proves every consequence available from the exact yes payload and does
not manufacture the missing route-8 collection, basin burden, private-carrier
injection, or boundary-deficiency estimates.
-/

/-- The strict coefficient gap used in the final carrier squeeze. -/
theorem p13Route8CollisionCoefficientGap
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node146 : P13Node146To147 ctx node21) :
    p13Route8Tau (p13PackingTheta ctx) <
      12 * ((1 : ℚ) / 4 - p13Route8Tau (p13PackingTheta ctx)) := by
  linarith [node146.tau_lt]

/-- Equivalent positive form of the fixed numerical margin. -/
theorem p13Route8CollisionMargin_pos
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node146 : P13Node146To147 ctx node21) :
    0 < 3 - 13 * p13Route8Tau (p13PackingTheta ctx) := by
  linarith [node146.tau_lt]

/-- Exact dependency-ready prefix of node `[147]`.  It adds only the two
algebraically equivalent strict margins.  The literal node-[146] payload is
retained by the framework state rather than copied into this structure.  It is not a
terminal outcome: the structural carrier ledgers required for contradiction
are deliberately absent from this type. -/
structure P13Node147ArithmeticPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4) where
  coefficientGap : p13Route8Tau (p13PackingTheta ctx) <
    12 * ((1 : ℚ) / 4 - p13Route8Tau (p13PackingTheta ctx))
  marginPositive : 0 < 3 - 13 * p13Route8Tau (p13PackingTheta ctx)

/-- Construct the complete arithmetic prefix from the exact green node-`[146]`
yes payload. -/
def p13Node147ArithmeticPrefix
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node146 : P13Node146To147 ctx node21) :
    P13Node147ArithmeticPrefix ctx node21 where
  coefficientGap := p13Route8CollisionCoefficientGap node146
  marginPositive := p13Route8CollisionMargin_pos node146

abbrev P13Node147ArithmeticStage
    (residual : P13Node145RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node146To147Stage
    (fun residual _node146 =>
      P13Node147ArithmeticPrefix residual.ctx residual.node21) residual

/-- Framework-owned `[146] -> [147]` handoff.  The application supplies only
the new arithmetic payload; all earlier facts and the exact predecessor remain
available in the accumulated state. -/
noncomputable def p13Node147ArithmeticRefinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node146To147Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      P13Node147ArithmeticStage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node146 => p13Node147ArithmeticPrefix node146)

/-- Node `[147]` adds no scan beyond reading the node-`[146]` payload and
combining its fixed rational inequality. -/
def p13Node147ArithmeticCheckCount
    (_result : P13Node147ArithmeticPrefix ctx node21) : Nat := 0

/-- The dependency-ready arithmetic prefix has constant local work. -/
theorem p13Node147ArithmeticCheckCount_polynomial
    (result : P13Node147ArithmeticPrefix ctx node21) :
    p13Node147ArithmeticCheckCount result ≤
      (ctx.G.object.input.vertices.card + 1) ^ 1 := by
  simp [p13Node147ArithmeticCheckCount]

end Erdos64EG.Internal
