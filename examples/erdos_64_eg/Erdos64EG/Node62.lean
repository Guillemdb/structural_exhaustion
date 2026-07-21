import Erdos64EG.Node61

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [62]: Type-A/Type-B high-surplus split

Node [62] consumes exactly the node-[61] successor.  Core owns the
dichotomy carrier.  The application supplies only the local predicate from
the graph layer: whether the connected negative support has a high-surplus
center.
-/

/-- Node [62]'s yes predicate: the node-[61] support has a high-surplus
center.  Bypass leaves stay inactive. -/
def Node62HighSurplus {V : Type u} {residual : InitialResidual V}
    (node61 : Node61Stage residual) : Prop :=
  match node61 with
  | ⟨⟨⟨⟨.bypass _, _node57⟩, _node58⟩, _node60⟩, _output⟩ =>
      False
  | ⟨⟨⟨⟨.degraded _data _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      output.support.HasHighSurplus
  | ⟨⟨⟨⟨.alternate _data _ _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      output.support.HasHighSurplus

/-- Node [62]'s no predicate: the same node-[61] support has no high-surplus
center.  Bypass leaves stay inactive and are preserved by Core. -/
def Node62NoHighSurplus {V : Type u} {residual : InitialResidual V}
    (node61 : Node61Stage residual) : Prop :=
  match node61 with
  | ⟨⟨⟨⟨.bypass _, _node57⟩, _node58⟩, _node60⟩, _output⟩ =>
      True
  | ⟨⟨⟨⟨.degraded _data _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      output.support.NoHighSurplus
  | ⟨⟨⟨⟨.alternate _data _ _node56, _node57⟩, _node58⟩, _node60⟩, output⟩ =>
      output.support.NoHighSurplus

noncomputable def node62HighSurplusDecidable {V : Type u}
    {residual : InitialResidual V} (node61 : Node61Stage residual) :
    Decidable (Node62HighSurplus node61) := by
  classical
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
                      exact isFalse id
                  | degraded data node56Output =>
                      change Decidable
                        output.support.HasHighSurplus
                      infer_instance
                  | alternate data low node56Output =>
                      change Decidable
                        output.support.HasHighSurplus
                      infer_instance

theorem node62NoHighSurplus_of_not_high {V : Type u}
    {residual : InitialResidual V} (node61 : Node61Stage residual)
    (notHigh : ¬ Node62HighSurplus node61) :
    Node62NoHighSurplus node61 := by
  classical
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
                      exact trivial
                  | degraded data node56Output =>
                      change output.support.NoHighSurplus
                      exact output.support.noHighSurplus_of_not_hasHigh
                        (by
                          intro high
                          exact notHigh high)
                  | alternate data low node56Output =>
                      change output.support.NoHighSurplus
                      exact output.support.noHighSurplus_of_not_hasHigh
                        (by
                          intro high
                          exact notHigh high)

/-- The complete carrier after node [62]. -/
abbrev Node62Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecision
    (@Node61Stage V) (@Node62HighSurplus V) (@Node62NoHighSurplus V)
    residual

/-- Framework-owned node-[62] dichotomy. -/
noncomputable def node62P13HighSurplusSplit {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node61Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node62Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideUsingStage
    (fun _residual node61 => node62HighSurplusDecidable node61)
    (fun _residual node61 notHigh =>
      node62NoHighSurplus_of_not_high node61 notHigh)

noncomputable def runInitialThroughNode62 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode61 residual).mapYesStage
    node62P13HighSurplusSplit

def node62LocalChecks : Nat := 0

theorem node62LocalChecks_eq_zero : node62LocalChecks = 0 := rfl

end Erdos64EG.Internal
