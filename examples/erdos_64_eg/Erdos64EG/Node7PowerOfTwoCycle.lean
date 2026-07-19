import Erdos64EG.Node6MersenneDecision

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [7]: the CT1 target terminal

This node continues only node `[6]`'s literal C1 constructor.  The framework
derives the public power-of-two target from the stored CT1 certificate and
retains the avoiding constructor unchanged for node `[8]`.
-/

abbrev Node7Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node6Stage V)
    (fun current node6 =>
      CT1.ResidualRefinement.CertificatePublicTargetContinuation
        (mersenneReturnEncoding V)
        (node6Input (residual := current) node6.previous))
    residual

noncomputable def node7PowerOfTwoCycle {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node6Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node7Stage V) :=
  CT1.ResidualRefinement.continueCertificatePublicTargetUsingStage
    (mersenneReturnEncoding V) fun _residual node5 => node6Input node5

noncomputable def runInitialThroughNode7 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode6 residual).mapYesStage node7PowerOfTwoCycle

/-- The literal C1 branch contains the exact official power-of-two target. -/
theorem node7_cycle {V : Type u} {residual : InitialResidual V}
    (stage : Node7Stage residual) :
    match stage.output with
    | .c1 _ _target => Target stage.previous.previous.previous.context.G
    | .avoiding _ => True := by
  cases stage.output with
  | c1 run target => exact target
  | avoiding run => trivial

/-- Node `[7]` performs no work beyond the retained CT1 certificate check. -/
theorem node7_work {V : Type u} {residual : InitialResidual V}
    (stage : Node7Stage residual) :
    match stage.output with
    | .c1 run _ => run.checks ≤ 1
    | .avoiding run => run.checks ≤ 1 := by
  cases stage.output with
  | c1 run target => exact CT1.certifiedC1Run_checks_le run
  | avoiding run =>
      change run.checks ≤ 1
      rw [run.checks_eq]
      exact Nat.zero_le _

#print axioms runInitialThroughNode7
#print axioms node7_cycle
#print axioms node7_work

end Erdos64EG.Internal
