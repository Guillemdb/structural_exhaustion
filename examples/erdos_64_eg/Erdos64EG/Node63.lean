import Erdos64EG.Node64
import StructuralExhaustion.Routes.NegativeSupportHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [63]: Type-A no-high handoff

Node [63] is the no edge of node [62], completed after node [64]'s yes
handoff.  Core preserves the Type-B yes output and attaches the Type-A
no-high route only to the no branch.
-/

/-- Node [63]'s no-edge output. -/
abbrev Node63Output {V : Type u} {residual : InitialResidual V}
    (node61 : Node61Stage residual)
    (noHigh : Node62NoHighSurplus node61) : Type (u + 2) :=
  match node61 with
  | ⟨⟨⟨⟨.bypass _, _node57⟩, _node58⟩, _node60⟩, _output⟩ =>
      PUnit.{u + 3}
  | ⟨⟨⟨⟨.degraded _data _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      ULift.{u + 2, u}
        (StructuralExhaustion.Routes.NegativeSupportHandoff.NoHighTypedResidual
          node62P13ChargeParameters node62P13HighThreshold
          (StructuralExhaustion.Graph.NegativeSupportHandoff.chargeProfileWith
            output.ctx.G.object node62P13ChargeParameters node62P13HighThreshold
            output.support.core).positiveDeficiency
          output.support.core.card output.support)
  | ⟨⟨⟨⟨.alternate _data _ _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      ULift.{u + 2, u}
        (StructuralExhaustion.Routes.NegativeSupportHandoff.NoHighTypedResidual
          node62P13ChargeParameters node62P13HighThreshold
          (StructuralExhaustion.Graph.NegativeSupportHandoff.chargeProfileWith
            output.ctx.G.object node62P13ChargeParameters node62P13HighThreshold
            output.support.core).positiveDeficiency
          output.support.core.card output.support)

theorem node63P13BudgetNegative {V : Type u}
    {object : StructuralExhaustion.Graph.FiniteObject V}
    (support :
      StructuralExhaustion.Graph.NegativeSupportHandoff.ConnectedNegativeSupportWith
        object node62P13ChargeParameters node62P13HighThreshold)
    (noHigh : support.NoHighSurplus) :
    (node62P13ChargeParameters.scale : Int) *
        (((StructuralExhaustion.Graph.NegativeSupportHandoff.chargeProfileWith
          object node62P13ChargeParameters
          node62P13HighThreshold support.core).positiveDeficiency : Int)) -
      (support.core.card : Int) < 0 := by
  have surplusZero := support.assignedSurplus_eq_zero_of_noHigh noHigh
  have negative := support.negative
  unfold StructuralExhaustion.Graph.AssignedSupportCharge.ParameterizedProfile.netCharge
    at negative
  rw [surplusZero] at negative
  simpa [StructuralExhaustion.Graph.NegativeSupportHandoff.chargeProfileWith] using
      negative

noncomputable def node63OutputOfNoHigh {V : Type u}
    {residual : InitialResidual V} (node61 : Node61Stage residual)
    (noHigh : Node62NoHighSurplus node61) :
    Node63Output node61 noHigh := by
  cases node61 with
  | mk node60 output =>
      cases node60 with
      | mk node58 node60Proof =>
          cases node58 with
          | mk node57 node58Output =>
              cases node57 with
              | mk node56 node57Output =>
                  cases node56 with
                  | bypass data =>
                      exact PUnit.unit
                  | degraded data node56Output =>
                      exact ULift.up
                        (StructuralExhaustion.Routes.NegativeSupportHandoff.noHighTyped
                          node62P13ChargeParameters node62P13HighThreshold
                          (StructuralExhaustion.Graph.NegativeSupportHandoff.chargeProfileWith
                            output.ctx.G.object node62P13ChargeParameters
                            node62P13HighThreshold
                            output.support.core).positiveDeficiency
                          output.support.core.card
                          output.support node62P13HighThreshold_eq
                          output.ctx.baseline noHigh
                          (node63P13BudgetNegative output.support noHigh))
                  | alternate data low node56Output =>
                      exact ULift.up
                        (StructuralExhaustion.Routes.NegativeSupportHandoff.noHighTyped
                          node62P13ChargeParameters node62P13HighThreshold
                          (StructuralExhaustion.Graph.NegativeSupportHandoff.chargeProfileWith
                            output.ctx.G.object node62P13ChargeParameters
                            node62P13HighThreshold
                            output.support.core).positiveDeficiency
                          output.support.core.card
                          output.support node62P13HighThreshold_eq
                          output.ctx.baseline noHigh
                          (node63P13BudgetNegative output.support noHigh))

/-- The complete Part-V carrier after both node-[62] branches have been
routed to their paper continuations. -/
abbrev Node63Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionNoAfterYes
    (@Node61Stage V) (@Node62HighSurplus V) (@Node62NoHighSurplus V)
    (fun residual node61 high => Node64Output (residual := residual) node61 high)
    (fun residual node61 noHigh =>
      Node63Output (residual := residual) node61 noHigh)
    residual

/-- Framework-owned node-[63] no continuation after node [64]. -/
noncomputable def node63P13TypeAHandoff {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node64Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node63Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionNoAfterYes
    (fun _residual node61 noHigh => node63OutputOfNoHigh node61 noHigh)

noncomputable def runInitialThroughNode63 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode64 residual).mapYesStage
    node63P13TypeAHandoff

def node63LocalChecks : Nat := 0

theorem node63LocalChecks_eq_zero : node63LocalChecks = 0 := rfl

end Erdos64EG.Internal
