import Hypostructure.CT1.Execution
import Hypostructure.Core.Residual.Decision

/-!
# CT1 proof-carrying target certificates

This execution mode is for targets whose witness is already mathematical data.
It classically decides the external target, validates exactly one encoded code
on the successful arm, and performs no code scan on the avoiding arm.  There is
deliberately no code universe or enumeration in this API.
-/

namespace Hypostructure.CT1

universe uPrevious uCode

/-- Domain-neutral proof-carrying representation of an external target. -/
structure CertificateEncoding (Previous : Type uPrevious)
    (PublicTarget : Previous -> Prop) where
  Code : Previous -> Type uCode
  Accepts : (previous : Previous) -> Code previous -> Prop
  encode : forall {previous}, PublicTarget previous ->
    Exists fun code => Accepts previous code
  decode : forall {previous code}, Accepts previous code ->
    PublicTarget previous
  acceptsDecidable : (previous : Previous) -> (code : Code previous) ->
    Decidable (Accepts previous code)

namespace CertificateEncoding

/-- One framework-validated code at the literal predecessor. -/
structure AcceptedCode {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) where
  private mk ::
  code : encoding.Code previous
  accepted : encoding.Accepts previous code

/-- Core's proposition/complement branch for the external target. -/
abbrev PublicTargetDecision {Previous : Type uPrevious}
    (PublicTarget : Previous -> Prop) (previous : Previous) :=
  Core.Residual.Decision.Binary PublicTarget
    (fun current => Not (PublicTarget current)) previous

/-- Ask Core to choose the target/complement branch using classical
decidability.  The application never receives a branch constructor. -/
noncomputable def decidePublicTarget {Previous : Type uPrevious}
    (PublicTarget : Previous -> Prop) (previous : Previous) :
    PublicTargetDecision PublicTarget previous :=
  ((Core.Residual.Decision.Node.complement PublicTarget
    (fun current => Classical.propDecidable (PublicTarget current))).run
      previous).added

private def validateAcceptedCode {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    {previous : Previous} (code : encoding.Code previous)
    (accepted : encoding.Accepts previous code) :
    AcceptedCode encoding previous :=
  match encoding.acceptsDecidable previous code with
  | .isTrue checked => .mk code checked
  | .isFalse rejected => (rejected accepted).elim

/-- Framework-owned target route.  Its private constructor ties a Core-owned
decision to the one validated code required only by the successful arm. -/
structure Route {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) where
  private mk ::
  decision : PublicTargetDecision PublicTarget previous
  validation :
    match decision with
    | .yesBranch _target => AcceptedCode encoding previous
    | .noBranch _avoids => PUnit

namespace Route

/-- Semantic terminal forced by the Core decision. -/
def terminal {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous) : Terminal :=
  match route.decision with
  | .yesBranch _ => .c1
  | .noBranch _ => .avoiding

/-- Exact primitive acceptance checks performed by this route. -/
def checks {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous) : Nat :=
  match route.decision with
  | .yesBranch _ => 1
  | .noBranch _ => 0

/-- Recover the accepted code only after the route is known to be successful. -/
def acceptedCode {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous)
    (isC1 : route.terminal = .c1) : AcceptedCode encoding previous := by
  rcases route with ⟨decision, validation⟩
  cases decision with
  | yesBranch _target => exact validation
  | noBranch _avoids => simp [terminal] at isC1

/-- The exact check count is determined by the semantic terminal. -/
theorem checks_eq_terminal {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous) :
    route.checks = match route.terminal with
      | .c1 => 1
      | .avoiding => 0 := by
  rcases route with ⟨decision, validation⟩
  cases decision <;> rfl

end Route

/-- Classically select the public-target branch and validate the one code
selected from `encode` on the successful arm. -/
noncomputable def routePublicTarget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) : Route encoding previous := by
  cases decision : decidePublicTarget PublicTarget previous with
  | yesBranch target =>
      let code := Classical.choose (encoding.encode target)
      have accepted : encoding.Accepts previous code :=
        Classical.choose_spec (encoding.encode target)
      exact .mk (.yesBranch target)
        (validateAcceptedCode encoding code accepted)
  | noBranch avoids =>
      exact .mk (.noBranch avoids) PUnit.unit

/-- Semantic proposition certified by a certificate-mode terminal. -/
def OutcomeClaim {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (_encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) : Terminal -> Prop
  | .c1 => PublicTarget previous
  | .avoiding => Not (PublicTarget previous)

/-- A routed successful code decodes to the public target, while the other
Core branch is literal target avoidance. -/
theorem Route.verified {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous) :
    OutcomeClaim encoding previous route.terminal := by
  rcases route with ⟨decision, validation⟩
  cases decision with
  | yesBranch _target =>
      exact encoding.decode validation.accepted
  | noBranch avoids =>
      exact avoids

/-- If the public target is impossible at the retained predecessor, Core's
route is necessarily the exact avoiding terminal. -/
theorem Route.terminal_avoiding_of_not_target {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous)
    (avoids : Not (PublicTarget previous)) : route.terminal = .avoiding := by
  cases terminal : route.terminal with
  | c1 =>
      have target : PublicTarget previous := by
        simpa [OutcomeClaim, terminal] using route.verified
      exact (avoids target).elim
  | avoiding => rfl

/-- Audit nodes for certificate-driven CT1.  The avoiding route contains no
certificate-validation node because it performs no primitive scan. -/
inductive TraceNodeId where
  | entry
  | publicTargetDecision
  | certificateValidation
  | c1Terminal
  | avoidingTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed certificate trace. -/
inductive TypedTrace : Terminal -> Type where
  | c1 : TypedTrace .c1
  | avoiding : TypedTrace .avoiding

namespace TypedTrace

/-- Observable nodes of a certificate-mode trace. -/
def nodes : {terminal : Terminal} -> TypedTrace terminal -> List TraceNodeId
  | .c1, .c1 =>
      [.entry, .publicTargetDecision, .certificateValidation, .c1Terminal]
  | .avoiding, .avoiding =>
      [.entry, .publicTargetDecision, .avoidingTerminal]

/-- Canonical node sequence for each terminal. -/
def expectedNodes : Terminal -> List TraceNodeId
  | .c1 =>
      [.entry, .publicTargetDecision, .certificateValidation, .c1Terminal]
  | .avoiding =>
      [.entry, .publicTargetDecision, .avoidingTerminal]

/-- The terminal index fixes the complete certificate trace. -/
theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : TypedTrace terminal) -> trace.nodes = expectedNodes terminal
  | .c1, .c1 => rfl
  | .avoiding, .avoiding => rfl

end TypedTrace

/-- Framework-selected trace for a routed certificate result. -/
def traceOfRoute {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {previous : Previous} (route : Route encoding previous) :
    TypedTrace route.terminal := by
  rcases route with ⟨decision, validation⟩
  cases decision with
  | yesBranch _target => exact .c1
  | noBranch _avoids => exact .avoiding

/-- The complete predecessor ledger extended by exactly one framework-owned
certificate route. -/
abbrev Stage {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget) :=
  Core.Residual.Ledger.Extension Previous fun previous => Route encoding previous

/-- Framework-owned evidence that an impossible C1 branch has been discharged
and the literal CT1 stage lies on its avoiding arm.  The evidence stores only
the generated terminal equality; target avoidance is recovered from CT1
soundness rather than copied into another application payload. -/
structure AvoidingEvidence {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (stage : Stage encoding) where
  private mk ::
  terminal_eq : stage.added.terminal = .avoiding

namespace AvoidingEvidence

/-- Recover exact public-target avoidance from the retained CT1 route. -/
theorem avoids {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {stage : Stage encoding} (evidence : AvoidingEvidence encoding stage) :
    Not (PublicTarget stage.previous) := by
  simpa [OutcomeClaim, evidence.terminal_eq] using stage.added.verified

/-- The retained avoiding route performs no certificate validation. -/
theorem checks_eq_zero {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {stage : Stage encoding} (evidence : AvoidingEvidence encoding stage) :
    stage.added.checks = 0 := by
  rw [stage.added.checks_eq_terminal, evidence.terminal_eq]

/-- The retained route has exactly the framework's avoiding trace. -/
theorem trace_exact {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    {stage : Stage encoding} (evidence : AvoidingEvidence encoding stage) :
    (traceOfRoute stage.added).nodes = TypedTrace.expectedNodes .avoiding := by
  rw [(traceOfRoute stage.added).nodes_eq_expected, evidence.terminal_eq]

end AvoidingEvidence

/-- Exact successor after the C1 arm has been closed.  Its predecessor is the
literal CT1 decision stage, so the complete accumulated ledger is retained. -/
abbrev AvoidingSuccessorStage {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget) :=
  Core.Residual.Ledger.Extension (Stage encoding) fun stage =>
    AvoidingEvidence encoding stage

/-- Discharge the C1 arm using the inherited public-target contradiction and
continue with the exact avoiding arm.  CT1 owns the terminal inspection and
ledger extension. -/
def continueAvoiding {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Not (PublicTarget stage.previous)) :
    AvoidingSuccessorStage encoding :=
  Core.Residual.Ledger.extend stage
    { terminal_eq :=
        stage.added.terminal_avoiding_of_not_target targetImpossible }

@[simp] theorem continueAvoiding_previous {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (stage : Stage encoding)
    (targetImpossible : Not (PublicTarget stage.previous)) :
    (encoding.continueAvoiding stage targetImpossible).previous = stage :=
  rfl

/-- Closed certificate-mode result.  Only CT1 can construct the terminal,
ledger extension, trace, and exact work count as one coherent value. -/
structure ExecutionResult {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget) where
  private mk ::
  stage : Stage encoding
  trace : TypedTrace stage.added.terminal
  checks : Nat
  checks_eq : checks = stage.added.checks

namespace ExecutionResult

/-- Terminal selected by the framework-owned route. -/
def terminal {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) : Terminal :=
  result.stage.added.terminal

/-- Observable exact trace. -/
def traceNodes {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) : List TraceNodeId :=
  result.trace.nodes

/-- Recover the accepted code from a completed C1 result. -/
def acceptedCode {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) (isC1 : result.terminal = .c1) :
    AcceptedCode encoding result.stage.previous :=
  result.stage.added.acceptedCode isC1

/-- Aggregate semantic soundness. -/
theorem verified {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) :
    OutcomeClaim encoding result.stage.previous result.terminal :=
  result.stage.added.verified

/-- Every typed trace is exactly the reference trace for its terminal. -/
theorem trace_exact {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) :
    result.traceNodes = TypedTrace.expectedNodes result.terminal :=
  result.trace.nodes_eq_expected

/-- Public target truth forces C1. -/
theorem terminal_c1_of_target {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding)
    (target : PublicTarget result.stage.previous) :
    result.terminal = .c1 := by
  cases terminal : result.terminal with
  | c1 => rfl
  | avoiding =>
      have avoids : Not (PublicTarget result.stage.previous) := by
        simpa [OutcomeClaim, terminal] using result.verified
      exact (avoids target).elim

/-- Exact public target avoidance forces the avoiding terminal. -/
theorem terminal_avoiding_of_not_target {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding)
    (avoids : Not (PublicTarget result.stage.previous)) :
    result.terminal = .avoiding := by
  cases terminal : result.terminal with
  | c1 =>
      have target : PublicTarget result.stage.previous := by
        simpa [OutcomeClaim, terminal] using result.verified
      exact (avoids target).elim
  | avoiding => rfl

/-- Every successful certificate run performs exactly one validation. -/
theorem checks_eq_one_of_c1 {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) (isC1 : result.terminal = .c1) :
    result.checks = 1 := by
  rw [result.checks_eq, result.stage.added.checks_eq_terminal]
  change result.stage.added.terminal = .c1 at isC1
  rw [isC1]

/-- Every avoiding certificate run performs exactly zero code scans. -/
theorem checks_eq_zero_of_avoiding {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding)
    (isAvoiding : result.terminal = .avoiding) : result.checks = 0 := by
  rw [result.checks_eq, result.stage.added.checks_eq_terminal]
  change result.stage.added.terminal = .avoiding at isAvoiding
  rw [isAvoiding]

/-- Every certificate execution performs at most one primitive validation. -/
theorem checks_le_one {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) : result.checks <= 1 := by
  rw [result.checks_eq, result.stage.added.checks_eq_terminal]
  change (match result.terminal with | .c1 => 1 | .avoiding => 0) <= 1
  cases result.terminal <;> simp

end ExecutionResult

/-- Constant-one work budget for the successful validation arm. -/
def successfulValidationBudget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (_encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget) :
    Core.PolynomialCheckBudget Previous :=
  Core.PolynomialCheckBudget.constant (fun _previous => 0) 1

/-- Zero-scan work budget for exact public-target avoidance. -/
def avoidingBudget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (_encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget) :
    Core.PolynomialCheckBudget Previous :=
  Core.PolynomialCheckBudget.zero (fun _previous => 0)

/-- Uniform work envelope for the classically selected execution. -/
def executionBudget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget) :
    Core.PolynomialCheckBudget Previous :=
  successfulValidationBudget encoding

namespace ExecutionResult

/-- The C1 arm exactly consumes its constant-one validation budget. -/
theorem checks_eq_successfulBudget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) (isC1 : result.terminal = .c1) :
    result.checks =
      (successfulValidationBudget encoding).checks result.stage.previous := by
  change result.checks = 1
  exact result.checks_eq_one_of_c1 isC1

/-- The avoiding arm exactly consumes the zero-scan budget. -/
theorem checks_eq_avoidingBudget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding)
    (isAvoiding : result.terminal = .avoiding) :
    result.checks = (avoidingBudget encoding).checks result.stage.previous := by
  change result.checks = 0
  exact result.checks_eq_zero_of_avoiding isAvoiding

/-- Every result is bounded by the constant-one execution budget. -/
theorem checks_le_executionBudget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) :
    result.checks <= (executionBudget encoding).checks result.stage.previous := by
  change result.checks <= 1
  exact result.checks_le_one

/-- Every result satisfies the polynomial envelope carried by `Core.Budget`. -/
theorem checks_le_polynomial {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) :
    result.checks <= (executionBudget encoding).coefficient *
      ((executionBudget encoding).size result.stage.previous + 1) ^
        (executionBudget encoding).degree :=
  result.checks_le_executionBudget.trans
    ((executionBudget encoding).bounded result.stage.previous)

end ExecutionResult

/-- Execute proof-carrying CT1 on one literal incoming ledger. -/
noncomputable def runPublicTarget {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) : ExecutionResult encoding :=
  let routed := encoding.routePublicTarget previous
  .mk (Core.Residual.Ledger.extend previous routed) (traceOfRoute routed)
    routed.checks rfl

@[simp] theorem runPublicTarget_previous {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) :
    (encoding.runPublicTarget previous).stage.previous = previous :=
  rfl

/-- Certificate execution is total, sound, exactly traced, predecessor
preserving, and polynomially work-bounded. -/
theorem runPublicTarget_total {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) :
    Exists fun result : ExecutionResult encoding =>
      result.stage.previous = previous ∧
      OutcomeClaim encoding previous result.terminal ∧
      result.traceNodes = TypedTrace.expectedNodes result.terminal ∧
      result.checks <= (executionBudget encoding).coefficient *
        ((executionBudget encoding).size previous + 1) ^
          (executionBudget encoding).degree := by
  let result := encoding.runPublicTarget previous
  refine ⟨result, rfl, result.verified, result.trace_exact, ?_⟩
  exact result.checks_le_polynomial

/-- The canonical proof-carrying executor is deterministic in relational form. -/
theorem runPublicTarget_deterministic {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    (encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget)
    (previous : Previous) (first second : ExecutionResult encoding)
    (firstIsRun : first = encoding.runPublicTarget previous)
    (secondIsRun : second = encoding.runPublicTarget previous) :
    first = second :=
  firstIsRun.trans secondIsRun.symm

/-- No terminal outside C1 and exact avoidance is reachable. -/
theorem outcome_exhaustive {Previous : Type uPrevious}
    {PublicTarget : Previous -> Prop}
    {encoding : CertificateEncoding.{uPrevious, uCode} Previous PublicTarget}
    (result : ExecutionResult encoding) :
    result.terminal = .c1 ∨ result.terminal = .avoiding := by
  cases result.terminal <;> simp

end CertificateEncoding

end Hypostructure.CT1
