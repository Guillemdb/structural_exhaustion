import Hypostructure.CT16.Search

/-!
# CT16 accumulated execution

The complete generated payload is appended once to the literal predecessor.
Its constructor is private, so applications cannot choose a terminal, trace,
outcome, or work count.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Semantic CT16 terminals. -/
inductive Terminal where
  | properSupport
  | exactCode
  | mismatch
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT16 reference trace. -/
inductive NodeId where
  | entry
  | coordinateSchedule
  | supportScan
  | closedCodeComputation
  | codeEqualityDecision
  | properSupportTerminal
  | exactCodeTerminal
  | mismatchTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed reference traces. -/
inductive Trace : Terminal -> Type where
  | properSupport : Trace .properSupport
  | exactCode : Trace .exactCode
  | mismatch : Trace .mismatch

namespace Trace

/-- Observable nodes of a typed CT16 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .properSupport, .properSupport =>
      [.entry, .coordinateSchedule, .supportScan, .properSupportTerminal]
  | .exactCode, .exactCode =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .exactCodeTerminal]
  | .mismatch, .mismatch =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .mismatchTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .properSupport =>
      [.entry, .coordinateSchedule, .supportScan, .properSupportTerminal]
  | .exactCode =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .exactCodeTerminal]
  | .mismatch =>
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .mismatchTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .properSupport, .properSupport => rfl
  | .exactCode, .exactCode => rfl
  | .mismatch, .mismatch => rfl

end Trace

/-- Typed evidence attached to each generated terminal. -/
inductive Outcome {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) : Terminal -> Type _
  | properSupport (residual : ProperSupportResidual capability previous) :
      Outcome capability previous .properSupport
  | exactCode (certificate : ExactCodeCertificate capability previous) :
      Outcome capability previous .exactCode
  | mismatch (residual : ClosedTypeMismatchResidual capability previous) :
      Outcome capability previous .mismatch

/-- Closed-code work selected by each terminal.  Proper support stops before
the code computation; both whole-support terminals pay its exact registered
predecessor-indexed count. -/
def terminalCodeChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) : Terminal -> Nat
  | .properSupport => 0
  | .exactCode | .mismatch =>
      capability.codeComputation.budget.checks previous

/-- Equality work selected by each terminal.  It is executed only after whole
support and uses the exact registered predecessor-indexed count. -/
def terminalEqualityChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) : Terminal -> Nat
  | .properSupport => 0
  | .exactCode | .mismatch =>
      capability.equalityDecision.budget.checks previous

/-- Exact suffix work after the single support scan. -/
def terminalSuffixChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous)
    (terminal : Terminal) : Nat :=
  terminalCodeChecks capability previous terminal +
    terminalEqualityChecks capability previous terminal

/-- Complete framework-generated addition to the accumulated ledger. -/
structure Generated {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  supportExecution : Core.Finite.Search.Execution
    (capability.coordinatesAt previous)
    (fun coordinate => Not (spec.InSupport previous coordinate))
  supportExecution_eq : supportExecution = supportScan spec capability previous
  terminal : Terminal
  outcome : Outcome capability previous terminal
  trace : Trace terminal
  supportChecks : Nat
  supportChecks_eq : supportChecks =
    Core.Finite.Accounting.executionChecks supportExecution
  codeChecks : Nat
  codeChecks_eq : codeChecks =
    terminalCodeChecks capability previous terminal
  equalityChecks : Nat
  equalityChecks_eq : equalityChecks =
    terminalEqualityChecks capability previous terminal
  checks : Nat
  checks_eq : checks = supportChecks + (codeChecks + equalityChecks)

/-- Terminal-refined view of a generated proper-support branch. -/
structure ProperSupportOutput {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  residual : ProperSupportResidual capability previous

/-- Terminal-refined view of a generated exact-code branch. -/
structure ExactCodeOutput {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  certificate : ExactCodeCertificate capability previous

/-- Terminal-refined view of a generated closed-code mismatch branch. -/
structure MismatchOutput {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  residual : ClosedTypeMismatchResidual capability previous

/-- Execute all internal CT16 computations without changing the predecessor.

The support result is let-bound once.  Routing consumes that stored execution;
the support count is read from the same `Counted` value.  Whole-support branches
then let-bind exactly one counted code computation and exactly one counted
equality decision. -/
private def generate {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    Core.Counted (Generated spec capability previous) :=
  let supportResult := countedSupportScan spec capability previous
  let supportExecution := supportResult.value
  let routed := routeSupportExecution spec capability previous supportExecution
  match routed.added with
  | .yesBranch hasMissing =>
      let missing := routed.previous.hitOfHasHit hasMissing
      let generated : Generated spec capability previous := {
        supportExecution := supportExecution
        supportExecution_eq := rfl
        terminal := .properSupport
        outcome := .properSupport missing
        trace := .properSupport
        supportChecks := supportResult.checks
        supportChecks_eq := rfl
        codeChecks := 0
        codeChecks_eq := rfl
        equalityChecks := 0
        equalityChecks_eq := rfl
        checks := supportResult.checks
        checks_eq := rfl
      }
      ⟨generated, generated.checks⟩
  | .noBranch whole =>
      let codeResult := countedClosedCode capability previous whole
      let equalityResult :=
        countedRouteCode capability previous codeResult.value
      match equalityResult.value.added with
      | .yesBranch equal =>
          let generated : Generated spec capability previous := {
            supportExecution := supportExecution
            supportExecution_eq := rfl
            terminal := .exactCode
            outcome := .exactCode
              (ExactCodeCertificate.ofEquality
                equalityResult.value.previous equal)
            trace := .exactCode
            supportChecks := supportResult.checks
            supportChecks_eq := rfl
            codeChecks := codeResult.checks
            codeChecks_eq := countedClosedCode_checks capability previous whole
            equalityChecks := equalityResult.checks
            equalityChecks_eq := countedRouteCode_checks capability previous _
            checks := supportResult.checks +
              (codeResult.checks + equalityResult.checks)
            checks_eq := rfl
          }
          ⟨generated, generated.checks⟩
      | .noBranch notEqual =>
          let generated : Generated spec capability previous := {
            supportExecution := supportExecution
            supportExecution_eq := rfl
            terminal := .mismatch
            outcome := .mismatch
              (ClosedTypeMismatchResidual.ofInequality
                equalityResult.value.previous notEqual)
            trace := .mismatch
            supportChecks := supportResult.checks
            supportChecks_eq := rfl
            codeChecks := codeResult.checks
            codeChecks_eq := countedClosedCode_checks capability previous whole
            equalityChecks := equalityResult.checks
            equalityChecks_eq := countedRouteCode_checks capability previous _
            checks := supportResult.checks +
              (codeResult.checks + equalityResult.checks)
            checks_eq := rfl
          }
          ⟨generated, generated.checks⟩

namespace Generated

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
  {capability : Capability spec}
  {previous : Previous}

/-- Observable exact trace nodes selected by the generated terminal. -/
def traceNodes (generated : Generated spec capability previous) : List NodeId :=
  generated.trace.nodes

/-- Every output-only generation retains the canonical terminal trace. -/
theorem traceNodes_eq_expected
    (generated : Generated spec capability previous) :
    generated.traceNodes = Trace.expectedNodes generated.terminal :=
  Trace.nodes_eq_expected generated.trace

/-- The stored support count is exactly the canonical predecessor-owned scan. -/
theorem supportChecks_eq_canonical_scan
    (generated : Generated spec capability previous) :
    generated.supportChecks = Core.Finite.Accounting.executionChecks
      (supportScan spec capability previous) := by
  rw [generated.supportChecks_eq, generated.supportExecution_eq]

/-- Both the stored support execution and its stored count come from the same
single `countedSupportScan` result. -/
theorem supportExecution_eq_countedScan
    (generated : Generated spec capability previous) :
    generated.supportExecution =
      (countedSupportScan spec capability previous).value :=
  generated.supportExecution_eq

theorem supportChecks_eq_countedScan
    (generated : Generated spec capability previous) :
    generated.supportChecks =
      (countedSupportScan spec capability previous).checks :=
  generated.supportChecks_eq_canonical_scan

/-- Stored component counts are exactly those selected by the generated
terminal. -/
theorem codeChecks_eq_terminal
    (generated : Generated spec capability previous) :
    generated.codeChecks =
      terminalCodeChecks capability previous generated.terminal :=
  generated.codeChecks_eq

theorem equalityChecks_eq_terminal
    (generated : Generated spec capability previous) :
    generated.equalityChecks =
      terminalEqualityChecks capability previous generated.terminal :=
  generated.equalityChecks_eq

/-- Total checks are exactly the one canonical support scan plus the counted
code/equality suffix selected by the generated terminal. -/
theorem checks_eq_canonical_scan
    (generated : Generated spec capability previous) :
    generated.checks = Core.Finite.Accounting.executionChecks
        (supportScan spec capability previous) +
      terminalSuffixChecks capability previous generated.terminal := by
  rw [generated.checks_eq, generated.supportChecks_eq_canonical_scan,
    generated.codeChecks_eq, generated.equalityChecks_eq]
  rfl

/-- Proper support executes no code or equality suffix. -/
theorem checks_eq_properSupport
    (generated : Generated spec capability previous)
    (isProperSupport : generated.terminal = .properSupport) :
    generated.checks = generated.supportChecks := by
  rw [generated.checks_eq, generated.codeChecks_eq,
    generated.equalityChecks_eq, isProperSupport]
  rfl

/-- Exact code pays the exact code-computation and equality budgets. -/
theorem checks_eq_exactCode
    (generated : Generated spec capability previous)
    (isExactCode : generated.terminal = .exactCode) :
    generated.checks = generated.supportChecks +
      (capability.codeComputation.budget.checks previous +
        capability.equalityDecision.budget.checks previous) := by
  rw [generated.checks_eq, generated.codeChecks_eq,
    generated.equalityChecks_eq, isExactCode]
  rfl

/-- Code mismatch pays the same exact two counted suffix operations. -/
theorem checks_eq_mismatch
    (generated : Generated spec capability previous)
    (isMismatch : generated.terminal = .mismatch) :
    generated.checks = generated.supportChecks +
      (capability.codeComputation.budget.checks previous +
        capability.equalityDecision.budget.checks previous) := by
  rw [generated.checks_eq, generated.codeChecks_eq,
    generated.equalityChecks_eq, isMismatch]
  rfl

/-- Generated support scanning never exceeds the exact incoming schedule. -/
theorem supportChecks_le_card
    (generated : Generated spec capability previous) :
    generated.supportChecks ≤ (capability.coordinatesAt previous).card := by
  rw [generated.supportChecks_eq_canonical_scan]
  exact Core.Finite.Accounting.executionChecks_le_card
    (supportScan spec capability previous)

/-- Generated total work is bounded by the exact complete-schedule composition
of the support, code-computation, and equality budgets. -/
theorem checks_le_worstCase
    (generated : Generated spec capability previous) :
    generated.checks ≤ capability.worstCaseChecks previous := by
  rw [generated.checks_eq, generated.codeChecks_eq,
    generated.equalityChecks_eq, capability.worstCaseChecks_eq]
  have supportBound := generated.supportChecks_le_card
  cases generated.terminal <;>
    simp only [terminalCodeChecks, terminalEqualityChecks] <;> omega

/-- Output-indexed polynomial budget inherited from the exact complete-schedule
composition. -/
def workBudget
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    Core.PolynomialCheckBudget (Generated spec capability previous) where
  size := fun _generated => capability.completeWorkBudget.size previous
  checks := fun generated => generated.checks
  coefficient := capability.completeWorkBudget.coefficient
  degree := capability.completeWorkBudget.degree
  bounded := by
    intro generated
    exact generated.checks_le_worstCase.trans
      (capability.completeWorkBudget.bounded previous)

@[simp] theorem workBudget_size
    (generated : Generated spec capability previous) :
    (workBudget spec capability previous).size generated =
      capability.completeWorkBudget.size previous :=
  rfl

@[simp] theorem workBudget_checks
    (generated : Generated spec capability previous) :
    (workBudget spec capability previous).checks generated =
      generated.checks :=
  rfl

/-- Recover the first missing-coordinate residual only from the matching
generated terminal. -/
def properSupportResidual
    (generated : Generated spec capability previous)
    (isProperSupport : generated.terminal = .properSupport) :
    ProperSupportOutput capability previous := by
  rcases generated with
    ⟨supportExecution, supportExecution_eq, terminal, outcome, trace,
      supportChecks, supportChecks_eq, codeChecks, codeChecks_eq,
      equalityChecks, equalityChecks_eq, checks, checks_eq⟩
  cases outcome with
  | properSupport residual => exact ⟨residual⟩
  | exactCode _certificate => cases isProperSupport
  | mismatch _residual => cases isProperSupport

/-- Recover the exact-code certificate only from the matching generated
terminal. -/
def exactCodeCertificate
    (generated : Generated spec capability previous)
    (isExactCode : generated.terminal = .exactCode) :
    ExactCodeOutput capability previous := by
  rcases generated with
    ⟨supportExecution, supportExecution_eq, terminal, outcome, trace,
      supportChecks, supportChecks_eq, codeChecks, codeChecks_eq,
      equalityChecks, equalityChecks_eq, checks, checks_eq⟩
  cases outcome with
  | properSupport _residual => cases isExactCode
  | exactCode certificate => exact ⟨certificate⟩
  | mismatch _residual => cases isExactCode

/-- Recover the exact closed-code mismatch only from the matching generated
terminal. -/
def closedTypeMismatchResidual
    (generated : Generated spec capability previous)
    (isMismatch : generated.terminal = .mismatch) :
    MismatchOutput capability previous := by
  rcases generated with
    ⟨supportExecution, supportExecution_eq, terminal, outcome, trace,
      supportChecks, supportChecks_eq, codeChecks, codeChecks_eq,
      equalityChecks, equalityChecks_eq, checks, checks_eq⟩
  cases outcome with
  | properSupport _residual => cases isMismatch
  | exactCode _certificate => cases isMismatch
  | mismatch residual => exact ⟨residual⟩

end Generated

/-- Generate one exact CT16 terminal without wrapping the literal predecessor
in a ledger stage.  The caller supplies only the specification, capability,
and predecessor; CT16 owns the terminal, outcome, trace, and exact count. -/
def generateCounted {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    Core.Counted (Generated spec capability previous) :=
  generate spec capability previous

@[simp] theorem generateCounted_checks_eq_value {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generateCounted spec capability previous).checks =
      (generateCounted spec capability previous).value.checks :=
  by
    unfold generateCounted generate
    dsimp only
    split
    · rfl
    · split <;> rfl

/-- Exact total checks of output-only generation. -/
@[simp] theorem generateCounted_checks {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generateCounted spec capability previous).checks =
      Core.Finite.Accounting.executionChecks
          (supportScan spec capability previous) +
        terminalSuffixChecks capability previous
          (generateCounted spec capability previous).value.terminal := by
  rw [generateCounted_checks_eq_value]
  exact (generateCounted spec capability previous).value.checks_eq_canonical_scan

/-- Exact predecessor-indexed work budget for embedding CT16 generation in
another focused or routed framework executor. -/
def generationBudget {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.completeWorkBudget.size
  checks := fun previous => (generateCounted spec capability previous).checks
  coefficient := capability.completeWorkBudget.coefficient
  degree := capability.completeWorkBudget.degree
  bounded := by
    intro previous
    rw [generateCounted_checks_eq_value]
    exact (generateCounted spec capability previous).value.checks_le_worstCase.trans
      (capability.completeWorkBudget.bounded previous)

@[simp] theorem generationBudget_size {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generationBudget spec capability).size previous =
      capability.completeWorkBudget.size previous :=
  rfl

@[simp] theorem generationBudget_checks {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generationBudget spec capability).checks previous =
      Core.Finite.Accounting.executionChecks
          (supportScan spec capability previous) +
        terminalSuffixChecks capability previous
          (generateCounted spec capability previous).value.terminal := by
  change (generateCounted spec capability previous).checks = _
  exact generateCounted_checks spec capability previous

@[simp] theorem generateCounted_checks_eq_budget {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generateCounted spec capability previous).checks =
      (generationBudget spec capability).checks previous :=
  rfl

/-- Output-only generation never exceeds the exact complete-schedule
composition. -/
theorem generateCounted_checks_le_worstCase {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generateCounted spec capability previous).checks ≤
      capability.worstCaseChecks previous := by
  rw [generateCounted_checks_eq_value]
  exact (generateCounted spec capability previous).value.checks_le_worstCase

/-- The counted generator satisfies its exact predecessor-indexed generation
budget. -/
theorem generateCounted_checks_le_polynomial {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (generateCounted spec capability previous).checks ≤
      (generationBudget spec capability).coefficient *
        ((generationBudget spec capability).size previous + 1) ^
          (generationBudget spec capability).degree :=
  (generationBudget spec capability).bounded previous

/-- CT16's sole accumulated-ledger extension. -/
abbrev Stage {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Generated spec capability previous

/-- Closed result with private construction. -/
structure ExecutionResult {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability

namespace ExecutionResult

/-- Framework-derived terminal. -/
def terminal {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Typed terminal evidence generated by the runner. -/
def outcome {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Exact observable trace. -/
def traceNodes {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.stage.added.trace.nodes

/-- Exact support-scan check count. -/
def supportChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.supportChecks

/-- Exact closed-code computation count; zero on proper support. -/
def codeChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.codeChecks

/-- Exact target-code equality count; zero on proper support. -/
def equalityChecks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.equalityChecks

/-- Exact total primitive-check count. -/
def checks {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.checks

/-- Support scanning never exceeds the exact incoming coordinate count. -/
theorem supportChecks_le_card {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.supportChecks ≤
      (capability.coordinatesAt result.stage.previous).card := by
  rw [supportChecks, result.stage.added.supportChecks_eq]
  rw [result.stage.added.supportExecution_eq]
  exact _root_.Hypostructure.CT16.supportChecks_le_card
    spec capability result.stage.previous

/-- Exact total count is the composition of the three actually executed
components. -/
theorem checks_eq {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = result.supportChecks +
      (result.codeChecks + result.equalityChecks) :=
  result.stage.added.checks_eq

/-- Exact total count stated against the terminal-selected registered suffix. -/
theorem checks_eq_terminal {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = result.supportChecks +
      terminalSuffixChecks capability result.stage.previous result.terminal := by
  rw [result.checks_eq, codeChecks, equalityChecks,
    result.stage.added.codeChecks_eq, result.stage.added.equalityChecks_eq]
  rfl

/-- Every execution is bounded by the exact complete-schedule composition. -/
theorem checks_le_worstCase {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks ≤ capability.worstCaseChecks result.stage.previous :=
  result.stage.added.checks_le_worstCase

/-- Every generated execution satisfies CT16's composed polynomial envelope. -/
theorem checks_le_polynomial {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCoordinate, uCode} Previous}
    {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks ≤ (capability.completeWorkBudget).coefficient *
      ((capability.completeWorkBudget).size result.stage.previous + 1) ^
        (capability.completeWorkBudget).degree :=
  result.checks_le_worstCase.trans
    (capability.completeWorkBudget.bounded result.stage.previous)

end ExecutionResult

/-- Execute CT16 on one literal predecessor and append one generated payload. -/
def run {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  .mk (Core.Residual.Ledger.extend previous
    (generateCounted spec capability previous).value)

@[simp] theorem run_previous {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

@[simp] theorem run_checks_eq_generationBudget {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).checks =
      (generationBudget spec capability).checks previous :=
  (generateCounted_checks_eq_value spec capability previous).symm

end Hypostructure.CT16
