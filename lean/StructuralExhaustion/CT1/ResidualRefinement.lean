import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.CT1.ResidualRefinement

open StructuralExhaustion.Core

universe uAmbient uBranch uResidual uPrevious uCode uNext

/-- Exact two-way result of one proof-carrying CT1 target decision.  This is a
CT1-owned execution carrier, not an application route: each constructor stores
the canonical certified run for its terminal. -/
inductive CertificateDecision
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    (input : CT1.Input P) : Type (max (max uAmbient uBranch) uCode + 2) where
  | c1 (run : CT1.CertifiedC1Run encoding.spec input)
  | avoiding (run : CT1.CertifiedAvoidingRun encoding.spec input)

/-- One exhaustive proof-level target decision followed by exactly one
certificate-driven CT1 execution.  No target-code universe is generated. -/
noncomputable def decideCertificate
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    (input : CT1.Input P) : CertificateDecision encoding input := by
  by_cases target : PublicTarget input.context.G
  · let code := Classical.choose (encoding.encode target)
    have accepts := Classical.choose_spec (encoding.encode target)
    exact .c1 (encoding.run input code accepts)
  · exact .avoiding (encoding.runAvoiding input target)

/-- Retrieve one literal predecessor and execute the exhaustive
certificate-driven CT1 decision on that predecessor. -/
noncomputable def executeCertificateUsingStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    (input : (residual : Residual) → Previous residual → CT1.Input P)
    {facts : List (Residual → Prop)}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available Previous) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (Core.ResidualRefinement.State.DependentSuccessor Previous
        (fun residual previous =>
          CertificateDecision encoding (input residual previous))) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun residual previous =>
    decideCertificate encoding (input residual previous)

theorem CertificateDecision.verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    {encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget}
    {input : CT1.Input P} (decision : CertificateDecision encoding input) :
    match decision with
    | .c1 run => CT1.OutcomeClaim run.result.outcome
    | .avoiding run => CT1.OutcomeClaim run.result.outcome := by
  cases decision with
  | c1 run => exact run.result.verified
  | avoiding run => exact run.result.verified

theorem CertificateDecision.traceExact
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    {encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget}
    {input : CT1.Input P} (decision : CertificateDecision encoding input) :
    match decision with
    | .c1 run => run.result.trace =
        [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal]
    | .avoiding run => run.result.trace =
        [.entry, .equivalenceCertification, .realizationDecision,
          .avoidingTerminal] := by
  cases decision with
  | c1 run => exact run.trace_eq
  | avoiding run => exact run.trace_eq

theorem CertificateDecision.workBound
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    {encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget}
    {input : CT1.Input P} (decision : CertificateDecision encoding input) :
    match decision with
    | .c1 run => run.checks ≤ 1
    | .avoiding run => run.checks ≤ 1 := by
  cases decision with
  | c1 run => exact CT1.certifiedC1Run_checks_le run
  | avoiding run =>
      change run.checks ≤ 1
      rw [run.checks_eq]
      exact Nat.zero_le _

/-- The proof-carrying exhaustive executor is total for every inherited CT1
input. -/
theorem decideCertificate_total
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    (input : CT1.Input P) : Nonempty (CertificateDecision encoding input) :=
  ⟨decideCertificate encoding input⟩

/-- Recover the bridged public target from a stored certified C1 run. -/
theorem publicTarget_of_certifiedC1
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    {encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget}
    {input : CT1.Input P}
    (run : CT1.CertifiedC1Run encoding.spec input) :
    PublicTarget input.context.G := by
  rcases resultEq : run.result with ⟨terminal, path, outcome⟩
  cases outcome with
  | c1 certificate => exact encoding.bridge.publicTarget_of_c1 certificate
  | avoiding state =>
      have impossible : CT1.Graph.Terminal.avoiding = CT1.Graph.Terminal.c1 := by
        simpa [resultEq] using run.terminal_eq
      cases impossible

/-- Framework carrier for continuing only the C1 constructor of a
certificate decision.  The avoidance constructor is retained literally for
its separate downstream consumer. -/
inductive CertificatePublicTargetContinuation
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    (input : CT1.Input P) : Type (max (max uAmbient uBranch) uCode + 2) where
  | c1 (run : CT1.CertifiedC1Run encoding.spec input)
      (target : PublicTarget input.context.G)
  | avoiding (run : CT1.CertifiedAvoidingRun encoding.spec input)

/-- Continue the literal C1 edge of an accumulated certificate decision and
preserve its avoidance edge without reconstructing either branch. -/
noncomputable def continueCertificatePublicTargetUsingStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    (input : (residual : Residual) → Previous residual → CT1.Input P)
    {facts : List (Residual → Prop)}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (Core.ResidualRefinement.State.DependentSuccessor Previous
          (fun residual previous =>
            CertificateDecision encoding (input residual previous)))) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (Core.ResidualRefinement.State.DependentSuccessor
        (Core.ResidualRefinement.State.DependentSuccessor Previous
          (fun residual previous =>
            CertificateDecision encoding (input residual previous)))
        (fun residual decision =>
          CertificatePublicTargetContinuation encoding
            (input residual decision.previous))) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun _residual decision =>
    match decision.output with
    | .c1 run => .c1 run (publicTarget_of_certifiedC1 run)
    | .avoiding run => .avoiding run

/-- Framework carrier for continuing only the avoiding constructor of a
certificate decision.  The C1 constructor is retained literally, while the
avoiding constructor receives exactly one successor produced from its stored
run. -/
inductive CertificateAvoidingContinuation
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    (input : CT1.Input P)
    (Next : CT1.CertifiedAvoidingRun encoding.spec input → Type uPrevious) :
    Type (max (max (max uAmbient uBranch) uCode) uPrevious + 2) where
  | c1 (run : CT1.CertifiedC1Run encoding.spec input)
  | avoiding (run : CT1.CertifiedAvoidingRun encoding.spec input)
      (output : Next run)

/-- Continue the literal avoiding edge of an accumulated certificate
decision.  Branch retention and ledger extension are framework-owned; the
caller supplies only the mathematical successor on the avoiding run. -/
noncomputable def continueCertificateAvoidingUsingStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (encoding : CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode}
      PublicTarget)
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    (input : (residual : Residual) → Previous residual → CT1.Input P)
    {Next : (residual : Residual) → (previous : Previous residual) →
      CT1.CertifiedAvoidingRun encoding.spec (input residual previous) →
        Type uNext}
    (produce : (residual : Residual) → (previous : Previous residual) →
      (run : CT1.CertifiedAvoidingRun encoding.spec
        (input residual previous)) → Next residual previous run)
    {facts : List (Residual → Prop)}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (Core.ResidualRefinement.State.DependentSuccessor Previous
          (fun residual previous =>
            CertificateDecision encoding (input residual previous)))) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (Core.ResidualRefinement.State.DependentSuccessor
        (Core.ResidualRefinement.State.DependentSuccessor Previous
          (fun residual previous =>
            CertificateDecision encoding (input residual previous)))
        (fun residual decision =>
          CertificateAvoidingContinuation encoding
            (input residual decision.previous)
            (Next residual decision.previous))) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun residual decision =>
    match decision.output with
    | .c1 run => .c1 run
    | .avoiding run => .avoiding run
        (produce residual decision.previous run)

/-- The framework-owned output of one exhaustive CT1 execution on the literal
predecessor retrieved from an accumulated residual ledger. -/
abbrev ExhaustiveSuccessor
    {P : Core.Problem.{uAmbient, uBranch}} (S : CT1.Spec P)
    {Residual : Type uResidual} (Previous : Residual → Type uPrevious)
    (input : (residual : Residual) → Previous residual → CT1.Input P)
    (residual : Residual) :=
  Core.ResidualRefinement.State.DependentSuccessor Previous
    (fun current previous => CT1.ExecutionResult S (input current previous))
    residual

/-- Retrieve the exact predecessor once, execute CT1's reference runner once,
and let the refinement framework append the resulting terminal-indexed
execution to the same accumulated ledger. -/
noncomputable def executeUsingStage
    {P : Core.Problem.{uAmbient, uBranch}} (S : CT1.Spec P)
    (capability : CT1.Capability S)
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    (input : (residual : Residual) → Previous residual → CT1.Input P)
    {facts : List (Residual → Prop)}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available Previous) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (ExhaustiveSuccessor S Previous input) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun residual previous =>
    CT1.run S capability (input residual previous)

/-- The stored exhaustive successor has CT1's semantic soundness theorem. -/
theorem ExhaustiveSuccessor.verified
    {P : Core.Problem.{uAmbient, uBranch}} {S : CT1.Spec P}
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    {input : (residual : Residual) → Previous residual → CT1.Input P}
    {residual : Residual}
    (successor : ExhaustiveSuccessor S Previous input residual) :
    CT1.OutcomeClaim successor.output.outcome :=
  successor.output.verified

/-- The stored exhaustive successor retains CT1's exact typed trace. -/
theorem ExhaustiveSuccessor.traceValid
    {P : Core.Problem.{uAmbient, uBranch}} {S : CT1.Spec P}
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    {input : (residual : Residual) → Previous residual → CT1.Input P}
    {residual : Residual}
    (successor : ExhaustiveSuccessor S Previous input residual) :
    @CT1.Graph.ValidTrace P S (input residual successor.previous)
      successor.output.trace :=
  successor.output.traceValid

/-- Totality is inherited from the one stored reference execution; consumers
never rerun CT1 to recover it. -/
theorem ExhaustiveSuccessor.total
    {P : Core.Problem.{uAmbient, uBranch}} {S : CT1.Spec P}
    {Residual : Type uResidual} {Previous : Residual → Type uPrevious}
    {input : (residual : Residual) → Previous residual → CT1.Input P}
    {residual : Residual}
    (successor : ExhaustiveSuccessor S Previous input residual) :
    ∃ result : CT1.ExecutionResult S (input residual successor.previous),
      CT1.OutcomeClaim result.outcome ∧
        @CT1.Graph.ValidTrace P S (input residual successor.previous)
          result.trace :=
  ⟨successor.output, successor.verified, successor.traceValid⟩

/-- The exhaustive successor uses exactly the capability's existing local
polynomial search budget. -/
theorem work_polynomial
    {P : Core.Problem.{uAmbient, uBranch}} {S : CT1.Spec P}
    (capability : CT1.Capability S) (input : CT1.Input P) :
    (capability.polynomialBudget.checks input.context.G) ≤
      capability.polynomialBudget.coefficient *
        (capability.polynomialBudget.size input.context.G + 1) ^
          capability.polynomialBudget.degree :=
  capability.polynomialBudget.bounded input.context.G

end StructuralExhaustion.CT1.ResidualRefinement
