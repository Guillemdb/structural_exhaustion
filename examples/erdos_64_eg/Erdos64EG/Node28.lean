import Erdos64EG.Node27
import Erdos64EG.Shared.CT14P13PositiveDeficiency

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

structure Node28Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type (u + 1) where
  exactFormula :
    (p13RemainderDeficiencyProfile (Node21Context node18)).positiveDeficiency =
      Finset.sum (p13RemainderVertices (Node21Context node18))
        (fun vertex => 3 -
          (p13RemainderDeficiencyProfile
            (Node21Context node18)).internalDegree vertex)

abbrev Node28Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node28Output node18 bounded node21 low) residual

noncomputable def node28P13PositiveDeficiency {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node27Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node28Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node27Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node28Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (node27 : Node27Output node18 bounded node21 low) => by
      have _ := node27.noInternalThreeCore
      exact { exactFormula :=
        p13Remainder_positiveDeficiency_eq (Node21Context node18) }

noncomputable def runInitialThroughNode28 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode27 residual).mapYesStage
    node28P13PositiveDeficiency

def node28LocalChecks : Nat := 0
theorem node28LocalChecks_eq_zero : node28LocalChecks = 0 := rfl

#print axioms node28P13PositiveDeficiency
#print axioms runInitialThroughNode28

end Erdos64EG.Internal
