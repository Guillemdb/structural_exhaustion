import StructuralExhaustion.CT2.Automation

namespace StructuralExhaustion.Examples.CT2CertifiedReduction

open StructuralExhaustion

universe uAmbient uBranch

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : CT2.CertifiedReductionInput ctx)

/-! Kernel fixture for CT2's non-enumerative, certificate-driven profile. -/

def execution : CT2.CertifiedReductionRun ctx input :=
  CT2.runCertifiedReduction ctx input

example : (execution ctx input).terminal = .deletionC2 := rfl

example : (execution ctx input).trace =
    [.entry, .deletionDecision, .deletionC2Terminal] := rfl

example : (execution ctx input).checks = 1 := rfl

example : ∃ run : CT2.CertifiedReductionRun ctx input,
    run.terminal = .deletionC2 ∧
      run.trace = [.entry, .deletionDecision, .deletionC2Terminal] :=
  CT2.runCertifiedReduction_total ctx input

example : False := (execution ctx input).verified

example :
    (CT2.certifiedReductionBudget ctx).checks input ≤
      (CT2.certifiedReductionBudget ctx).coefficient *
        ((CT2.certifiedReductionBudget ctx).size input + 1) ^
          (CT2.certifiedReductionBudget ctx).degree :=
  (CT2.certifiedReductionBudget ctx).bounded input

end StructuralExhaustion.Examples.CT2CertifiedReduction
