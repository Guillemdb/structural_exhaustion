import Erdos64EG.Node26

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u


structure Node27Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type where
  noInternalThreeCore :
    (Node25Remainder node18).InternalMinDegreeFree 3
  noInternalSubgraphThreeCore :
    ¬(Node25Remainder node18).HasInternalSubgraphMinDegreeAtLeast 3

abbrev Node27Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node27Output node18 bounded node21 low) residual

noncomputable def node27P13NoInternalThreeCore {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node26Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node27Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node26Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node27Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (node26 : Node26Output node18 bounded node21 low) => by
      have exactRemainder := node26.canonicalRemainder
      constructor
      · simpa [exactRemainder] using
          p13Remainder_internalThreeCore_free (Node21Context node18)
      · simpa [exactRemainder] using
          p13Remainder_internalSubgraphThreeCore_free (Node21Context node18)

noncomputable def runInitialThroughNode27 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode26 residual).mapYesStage
    node27P13NoInternalThreeCore

def node27LocalChecks : Nat := 0
theorem node27LocalChecks_eq_zero : node27LocalChecks = 0 := rfl

#print axioms node27P13NoInternalThreeCore
#print axioms runInitialThroughNode27

end Erdos64EG.Internal
