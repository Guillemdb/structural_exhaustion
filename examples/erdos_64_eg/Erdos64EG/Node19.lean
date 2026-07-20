import Erdos64EG.Node18
import StructuralExhaustion.Core.OrderThresholdSplit
import StructuralExhaustion.Graph.SurplusClasswiseOverload

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [19]: exact non-near-cubic surplus decision

The literal node-[18] stage determines the selected graph. This node supplies
only the paper's fixed squared surplus comparison. The generic ordered-split
executor retrieves node [18], retains the full accumulated ledger, and creates
both exact diagram branches.
-/

/-- The fixed coefficient used by the paper's homogeneous-cap accounting. -/
def node19SurplusCoefficient : Nat :=
  450 * Graph.SurplusClasswiseOverload.maxCap 49 49 49 + 1

/-- The one ordered comparison introduced at node [19]. -/
noncomputable def node19Profile {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) :
    Core.OrderThresholdSplit.Profile Nat where
  value :=
    (Graph.InducedPathWindowLedger.totalSurplus
      (Node18StageContext node18).G.object) ^ 2
  threshold :=
    node19SurplusCoefficient *
      (Node18StageContext node18).G.object.input.vertices.card

/-- Framework specialization of node [19] to the exact node-[18] stage. -/
noncomputable def node19Family (V : Type u) :
    Core.OrderThresholdSplit.DependentProfileFamily
      (InitialResidual V) (@Node18Stage V) Nat where
  profile := fun _residual node18 => node19Profile node18

/-- Yes edge `[19] -> [20]`: strict non-near-cubic surplus. -/
abbrev Node19High {V : Type u} (residual : InitialResidual V)
    (node18 : Node18Stage residual) : Prop :=
  (node19Family V).StrictHigh residual node18

/-- No edge `[19] -> [21]`: the exact complementary squared bound. -/
abbrev Node19Low {V : Type u} (residual : InitialResidual V)
    (node18 : Node18Stage residual) : Prop :=
  (node19Family V).AtMost residual node18

abbrev Node19Stage {V : Type u} (residual : InitialResidual V) :=
  (node19Family V).StrictDecision residual

noncomputable def node19SurplusScaleDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node18Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node19Stage V) :=
  (node19Family V).executeStrictUsingStage

noncomputable def runInitialThroughNode19 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode18 residual).mapYesStage
    node19SurplusScaleDecision

theorem node19_exhaustive {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) :
    Node19High residual node18 ∨ Node19Low residual node18 :=
  (node19Family V).strictExhaustive node18

noncomputable def node19WorkBudget (V : Type u) :
    Core.PolynomialCheckBudget Unit :=
  (node19Family V).workBudget

theorem node19_work_zero (V : Type u) :
    (node19WorkBudget V).checks () = 0 :=
  (node19Family V).checks_eq_zero

#print axioms node19SurplusScaleDecision
#print axioms runInitialThroughNode19
#print axioms node19_exhaustive

end Erdos64EG.Internal
