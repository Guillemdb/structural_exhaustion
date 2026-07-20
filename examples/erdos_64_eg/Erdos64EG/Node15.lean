import Erdos64EG.Node14
import StructuralExhaustion.Graph.InducedPath

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-! Node [15]: framework-owned exhaustive `P₁₃`-free decision.

The paper edge is literally `[14] → [15]`.  The node-[14] stage already
retains the selected minimal context through its predecessor chain, so node
[15] consumes that immediate stage once.  `decideUsingStage` owns retrieval,
the exhaustive split, and preservation of the exact predecessor on both
constructors.
-/

abbrev Node15Input {V : Type u} (residual : InitialResidual V) :=
  Node14Stage residual

/-- The selected graph already carried by the immediate node-[14] stage. -/
abbrev Node15Context {V : Type u} {residual : InitialResidual V}
    (input : Node15Input residual) :=
  Node13Context input.previous

abbrev Node15P13Free {V : Type u} (residual : InitialResidual V)
    (input : Node15Input residual) : Prop :=
  Graph.InducedPathFree (Node15Context input).G.object.graph 13

abbrev Node15NotP13Free {V : Type u} (residual : InitialResidual V)
    (input : Node15Input residual) : Prop :=
  ¬ Node15P13Free residual input

abbrev Node15Decision {V : Type u} (residual : InitialResidual V) :=
  StructuralExhaustion.Core.ResidualRefinement.State.DependentDecision
    (Node15Input (V := V))
    (fun residual input => Node15P13Free residual input)
    (fun residual input => Node15NotP13Free residual input) residual

abbrev Node15Stage {V : Type u} (residual : InitialResidual V) :=
  Node15Decision residual

noncomputable def node15P13Decision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node14Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node15Stage V) := by
  classical
  exact Core.ResidualRefinement.State.StageNode.decideUsingStage
    (fun _residual _input => inferInstance)
    (fun _residual _input absent => absent)

noncomputable def runInitialThroughNode15 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode14 residual).mapYesStage node15P13Decision

theorem node15_exhaustive {V : Type u} {residual : InitialResidual V}
    (input : Node15Input residual) :
    Nonempty (Node15Decision residual) := by
  classical
  by_cases free : Node15P13Free residual input
  · exact ⟨.yesBranch input free⟩
  · exact ⟨.noBranch input free⟩

def node15LocalChecks : Nat := 0

theorem node15LocalChecks_eq_zero : node15LocalChecks = 0 := rfl

#print axioms node15P13Decision
#print axioms node15_exhaustive

end Erdos64EG.Internal
