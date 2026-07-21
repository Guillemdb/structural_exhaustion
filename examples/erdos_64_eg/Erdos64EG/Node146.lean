import Erdos64EG.Node145

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [146]: route-8 density threshold

Node [146] makes the paper's exact threshold decision
`78 * p13 < n` on the live node-[145] hot/cold residual.  The decision is
performed by Core on the active leaf of the accumulated node-[24]/node-[145]
cursor; all sibling constructors remain framework-owned bypass data.
-/

/-- The manuscript density `theta = p13 / n`, represented exactly. -/
noncomputable def node146PackingTheta
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ℚ :=
  (p13 ctx : ℚ) / ctx.G.object.input.vertices.card

/-- The manuscript's normalized route-8 load. -/
def node146Route8Tau (theta : ℚ) : ℚ :=
  15 * theta / (1 - 13 * theta)

abbrev Node146Bypass (V : Type u) (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYesBypass
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    residual

abbrev Node146Active (V : Type u) (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYesActive
    (@Node18Stage V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22Low V)
    (fun _residual _node18 _bounded _node21 _low => PUnit)
    residual

/-- The exact executable predicate at node `[146]`. -/
def Node146Route8BelowThreshold {V : Type u} {residual : InitialResidual V}
    (active : Node146Active V residual) : Prop :=
  78 * p13 (Node21Context active.previous) <
    (Node21Context active.previous).G.object.input.vertices.card

def Node146Route8NotBelow {V : Type u} {residual : InitialResidual V}
    (active : Node146Active V residual) : Prop :=
  ¬Node146Route8BelowThreshold active

private theorem node146VertexCount_pos
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    0 < ctx.G.object.input.vertices.card := by
  have baseline := (packedStaticInput.fixedContext ctx).baseline
  change 3 ≤ ctx.G.object.minDegree at baseline
  letI : Nonempty ctx.G.Vertex :=
    ctx.G.object.nonempty_of_minDegree_pos (by omega)
  let vertex : ctx.G.Vertex := Classical.choice inferInstance
  exact Nat.zero_lt_of_lt (ctx.G.object.degree_lt_vertexCount vertex)

theorem node146Route8BelowThreshold_iff_theta
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    78 * p13 ctx < ctx.G.object.input.vertices.card ↔
      node146PackingTheta ctx < (1 : ℚ) / 78 := by
  have nposNat := node146VertexCount_pos ctx
  have npos : (0 : ℚ) < ctx.G.object.input.vertices.card := by
    exact_mod_cast nposNat
  unfold node146PackingTheta
  constructor <;> intro h
  · apply (div_lt_iff₀ npos).2
    have hq : (78 : ℚ) * p13 ctx <
        ctx.G.object.input.vertices.card := by
      exact_mod_cast h
    norm_num
    linarith
  · have scaled := (div_lt_iff₀ npos).1 h
    have hq : (78 : ℚ) * p13 ctx <
        ctx.G.object.input.vertices.card := by
      norm_num at scaled
      linarith
    exact_mod_cast hq

theorem node146Route8Tau_lt_three_thirteenths_iff
    (theta : ℚ) (denominatorPositive : 0 < 1 - 13 * theta) :
    node146Route8Tau theta < (3 : ℚ) / 13 ↔
      theta < (1 : ℚ) / 78 := by
  unfold node146Route8Tau
  rw [div_lt_iff₀ denominatorPositive]
  constructor <;> intro h <;> linarith

theorem node146Route8_denominator_pos_of_below
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (below : 78 * p13 ctx < ctx.G.object.input.vertices.card) :
    0 < 1 - 13 * node146PackingTheta ctx := by
  have thetaLt := (node146Route8BelowThreshold_iff_theta ctx).mp below
  linarith

abbrev Node146DecisionStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (@Node146Bypass V) (@Node146Active V)
    (@Node146Route8BelowThreshold V) (@Node146Route8NotBelow V) residual

abbrev Node146Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (@Node146Bypass V) (@Node146Active V)
    (@Node146Route8BelowThreshold V) (@Node146Route8NotBelow V)
    (fun _residual _active _below => PUnit) residual

abbrev Node146To148Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (@Node146Bypass V) (@Node146Active V)
    (@Node146Route8BelowThreshold V) (@Node146Route8NotBelow V)
    (fun _residual _active _notBelow => PUnit) residual

noncomputable def node146Route8ThresholdDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node145Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node146DecisionStage V) :=
  Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoNoAfterYes
    (Current := fun _ _node18 _bounded _node21 _low => PUnit)
    (yes := @Node146Route8BelowThreshold V)
    (no := @Node146Route8NotBelow V)
    (fun _ active => by
      unfold Node146Route8BelowThreshold
      infer_instance)
    (fun _ _ absent => absent)

noncomputable def node146To147Refinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (@Node146DecisionStage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node146Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    fun _residual _active _below => PUnit.unit

noncomputable def node146To148Refinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (@Node146DecisionStage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node146To148Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    fun _residual _active _notBelow => PUnit.unit

noncomputable def runInitialThroughNode146Decision {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode145 residual).mapYesStage
    node146Route8ThresholdDecision

noncomputable def runInitialThroughNode146 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode146Decision residual).mapYesStage
    node146To147Refinement

noncomputable def runInitialThroughNode146To148 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode146Decision residual).mapYesStage
    node146To148Refinement

/-- Node [146] performs one primitive arithmetic comparison. -/
def node146LocalChecks : Nat := 1

theorem node146LocalChecks_eq_one : node146LocalChecks = 1 := rfl

#print axioms node146Route8ThresholdDecision
#print axioms node146To147Refinement
#print axioms node146To148Refinement
#print axioms runInitialThroughNode146
#print axioms runInitialThroughNode146To148

end Erdos64EG.Internal
