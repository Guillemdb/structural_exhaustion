import Erdos64EG.Node62
import StructuralExhaustion.Routes.NegativeSupportHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [64]: Type-B high-surplus handoff

Node [64] is the yes edge of node [62].  Core owns the continuation; the
application only converts the graph-layer high-surplus predicate on the exact
node-[61] support into the framework route payload consumed by Part VI.
-/

/-- Node [64]'s yes-edge output. -/
abbrev Node64Output {V : Type u} {residual : InitialResidual V}
    (node61 : Node61Stage residual)
    (high : Node62HighSurplus node61) : Type (u + 2) :=
  match node61 with
  | ⟨⟨⟨⟨.bypass _, _node57⟩, _node58⟩, _node60⟩, _output⟩ =>
      False.elim high
  | ⟨⟨⟨⟨.degraded _data _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      ULift.{u + 2, u}
        (StructuralExhaustion.Routes.NegativeSupportHandoff.OrdinaryResidualAtLeast
          node62P13ChargeParameters node62P13HighThreshold output.support)
  | ⟨⟨⟨⟨.alternate _data _ _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      ULift.{u + 2, u}
        (StructuralExhaustion.Routes.NegativeSupportHandoff.OrdinaryResidualAtLeast
          node62P13ChargeParameters node62P13HighThreshold output.support)

noncomputable def node64OutputOfHigh {V : Type u}
    {residual : InitialResidual V} (node61 : Node61Stage residual)
    (high : Node62HighSurplus node61) :
    Node64Output node61 high := by
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
                      exact False.elim high
                  | degraded data node56Output =>
                      exact ULift.up
                        (StructuralExhaustion.Routes.NegativeSupportHandoff.ordinaryAtLeast
                          node62P13ChargeParameters node62P13HighThreshold output.support
                          (output.support.highSurplusWitnessOfHasHigh high))
                  | alternate data low node56Output =>
                      exact ULift.up
                        (StructuralExhaustion.Routes.NegativeSupportHandoff.ordinaryAtLeast
                          node62P13ChargeParameters node62P13HighThreshold output.support
                          (output.support.highSurplusWitnessOfHasHigh high))

/-- The complete carrier after node [64]. -/
abbrev Node64Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionYesContinuation
    (@Node61Stage V) (@Node62HighSurplus V) (@Node62NoHighSurplus V)
    (fun residual node61 high => Node64Output (residual := residual) node61 high)
    residual

/-- Framework-owned node-[64] yes continuation. -/
noncomputable def node64P13TypeBHandoff {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node62Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node64Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionYes
    (fun _residual node61 high => node64OutputOfHigh node61 high)

noncomputable def runInitialThroughNode64 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode62 residual).mapYesStage
    node64P13TypeBHandoff

def node64LocalChecks : Nat := 0

theorem node64LocalChecks_eq_zero : node64LocalChecks = 0 := rfl

end Erdos64EG.Internal
