import Erdos64EG.Node25

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [26]: Residual A panel continuation

Node [26] introduces no second remainder and copies no node-[25] field.  It
records only that the Residual A entering Part II is definitionally the
canonical complement of the already selected maximum packing.
-/

/-- The sole node-[26] payload: the panel-entry name denotes exactly the
canonical remainder already fixed at node [25]. -/
structure Node26Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type where
  canonicalRemainder :
    Node25Remainder node18 = p13Remainder (Node21Context node18)

/-- The active cursor after the Part-I/Part-II boundary. -/
abbrev Node26Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node26Output node18 bounded node21 low) residual

/-- Framework-owned zero-copy `[25] -> [26]` continuation. -/
noncomputable def node26P13RemainderContinuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node25Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node26Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node25Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node26Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (_node25 : Node25Output node18 bounded node21 low) =>
      { canonicalRemainder := rfl }

noncomputable def runInitialThroughNode26 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode25 residual).mapYesStage
    node26P13RemainderContinuation

def node26LocalChecks : Nat := 0

theorem node26LocalChecks_eq_zero : node26LocalChecks = 0 := rfl

#print axioms node26P13RemainderContinuation
#print axioms runInitialThroughNode26

end Erdos64EG.Internal
