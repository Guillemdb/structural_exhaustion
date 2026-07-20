import Erdos64EG.Node21
import Erdos64EG.Shared.P13SequentialWindowLedger
import StructuralExhaustion.Core.OrderThresholdSplit

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [22]: exact `P₁₃` packing-density decision

The literal node-[21] payload lies on the no constructor of node [19].  Core
preserves node [19]'s other constructor and performs this new exhaustive
decision only on that payload.  The Erdős layer supplies just the two integers
in the manuscript's cross-multiplied density comparison.
-/

/-- Integer normalization of the printed window rate `118.108581006`. -/
def node22WindowRateNumerator : Nat := 118108581006

/-- Integer normalization of the near-cubic skeleton rate `1.5`. -/
def node22SkeletonRateNumerator : Nat := 1500000000

/-- The selected node-[17] packing count retained through node [21]. -/
noncomputable def node22PackingCount {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) : Nat :=
  node17PackingNumber node18.previous

/-- Node [22]'s sole local mathematical input: the exact finite comparison
whose strict side is the diagram's `yes` edge. -/
noncomputable def node22DensityFamily {V : Type u} :
    Core.OrderThresholdSplit.DependentNoContinuationProfileFamily
      (InitialResidual V) (@Node18Stage V) (@Node19Low V)
      (fun _residual node18 bounded => Node21Output node18 bounded) Nat where
  profile := fun _residual node18 _bounded _node21 =>
    {
      value := node22WindowRateNumerator * node22PackingCount node18
      threshold := node22SkeletonRateNumerator *
        (Node21Context node18).G.object.input.vertices.card
    }

abbrev Node22High {V : Type u} (residual : InitialResidual V)
    (node18 : Node18Stage residual) (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) : Prop :=
  (@node22DensityFamily V).StrictHigh residual node18 bounded node21

abbrev Node22Low {V : Type u} (residual : InitialResidual V)
    (node18 : Node18Stage residual) (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) : Prop :=
  (@node22DensityFamily V).AtMost residual node18 bounded node21

/-- Exact three-leaf carrier: the pre-existing node-[20] leaf, node [22]'s
strict `yes` edge to [23], and its complementary `no` edge to [24]. -/
abbrev Node22Stage {V : Type u} (residual : InitialResidual V) :=
  (@node22DensityFamily V).Decision (@Node19High V) residual

/-- Execute node [22] from the literal node-[21] accumulated stage. -/
noncomputable def node22P13DensityDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node21Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node22Stage V) :=
  (@node22DensityFamily V).executeStrictUsingNoContinuation

/-- The decision is exhaustive by the framework profile itself.  Its strict
constructor is node [23]'s input and its complementary constructor is node
[24]'s input; neither edge is supplied or excluded by a caller. -/
theorem node22DensityDecision_exhaustive {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    Node22High residual node18 bounded node21 ∨
      Node22Low residual node18 bounded node21 :=
  (@node22DensityFamily V).strictExhaustive node18 bounded node21

/-! Canonical framework runner for node [22].  Node [21] is executed by its
own `[19] no → [21]` continuation and its complete ledger is consumed by the
node-[22] decision. -/
noncomputable def runInitialThroughNode22 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode21 residual).mapYesStage
    node22P13DensityDecision

/-- Node [22] performs a proof-level comparison and no finite scan. -/
def node22LocalChecks : Nat := 0

theorem node22LocalChecks_eq_zero : node22LocalChecks = 0 := rfl

#print axioms node22P13DensityDecision
#print axioms node22DensityDecision_exhaustive
#print axioms runInitialThroughNode22

end Erdos64EG.Internal
