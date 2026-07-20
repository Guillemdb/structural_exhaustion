import Erdos64EG.Node6

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [7]: the CT1 target terminal

This node closes node `[6]`'s literal C1 constructor against the target
avoidance already carried by the selected minimal-counterexample context.
The framework derives the public power-of-two target from the stored CT1
certificate, performs the contradiction, and exposes only the exact avoiding
run for node `[8]`.
-/

abbrev Node7Stage {V : Type u} (residual : InitialResidual V) :=
  (node6Family V).AvoidingSuccessor residual

/-- The sole paper-local terminal fact at node `[7]`: a stored C1
certificate gives the official target, contradicting the inherited
counterexample avoidance theorem. -/
theorem node7CloseTarget {V : Type u} (_residual : InitialResidual V)
    (node5 : Node5Stage _residual)
    (run : CT1.CertifiedC1Run
      ((node6Family V).encoding _residual node5).spec
      ((node6Family V).input _residual node5)) : False :=
  node5.previous.context.avoids
    (CT1.ResidualRefinement.publicTarget_of_certifiedC1 run)

noncomputable def node7PowerOfTwoCycle {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node6Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts) (@Node7Stage V) :=
  (node6Family V).closePublicTargetContinueAvoidingUsingStage
    (fun residual node5 target => node5.previous.context.avoids target)

noncomputable def runInitialThroughNode7 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode6 residual).mapYesStage node7PowerOfTwoCycle

/-- The unique live output is the exact CT1 avoiding run on the literal
node-[5] predecessor. -/
theorem node7_avoids {V : Type u} {residual : InitialResidual V}
    (stage : Node7Stage residual) :
    ¬ Target (packedStaticInput.fixedContext
      stage.previous.previous.context).G :=
  stage.previous.previous.context.avoids

/-- Node `[7]` performs no work beyond the retained CT1 certificate check. -/
theorem node7_work {V : Type u} {residual : InitialResidual V}
    (stage : Node7Stage residual) :
    stage.output.checks = 0 :=
  stage.output.checks_eq

#print axioms runInitialThroughNode7
#print axioms node7CloseTarget
#print axioms node7_avoids
#print axioms node7_work

end Erdos64EG.Internal
