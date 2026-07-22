import Hypostructure.CT16.Execution

/-!
# CT16 counted output-only generation fixture

This fixture calls only `CT16.generateCounted`.  It exercises all three
generated terminals, exact accounting, terminal-refined accessors, literal
predecessor embedding, and delegation by the accumulated `run` API.
-/

namespace Hypostructure.Fixtures.CT16Generated

inductive Mode where
  | proper
  | exact
  | mismatch
  deriving DecidableEq, Repr

def coordinateSchedule : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

structure Residual where
  mode : Mode
  coordinates : Core.Finite.Enumeration (Fin 3)

abbrev Previous := Core.Residual.Ledger Residual

def inSupport : Mode -> Fin 3 -> Prop
  | .proper, coordinate => coordinate ≠ 1
  | .exact, _coordinate => True
  | .mismatch, _coordinate => True

def computedCode : Mode -> Bool
  | .proper => false
  | .exact => false
  | .mismatch => true

def spec : _root_.Hypostructure.CT16.Spec Previous where
  Coordinate := fun _previous => Fin 3
  InSupport := fun previous coordinate =>
    inSupport (Core.Residual.residualOf previous).mode coordinate
  ClosedCode := fun _previous => Bool
  closedCode := fun previous =>
    computedCode (Core.Residual.residualOf previous).mode
  targetCode := fun _previous => false

def codeCost : Mode -> Nat
  | .proper => 1
  | .exact => 2
  | .mismatch => 3

def codeComputationBudget : Core.PolynomialCheckBudget Previous where
  size := fun _previous => 0
  checks := fun previous =>
    codeCost (Core.Residual.residualOf previous).mode
  coefficient := 3
  degree := 0
  bounded := by
    intro previous
    cases mode : (Core.Residual.residualOf previous).mode <;>
      simp [codeCost]

def codeComputation :
    _root_.Hypostructure.CT16.ClosedCodeComputation spec where
  run := fun previous =>
    ⟨spec.closedCode previous,
      codeCost (Core.Residual.residualOf previous).mode⟩
  correct := by intros; rfl
  budget := codeComputationBudget
  checks_eq := by intros; rfl

def equalityDecision :
    _root_.Hypostructure.CT16.CodeEqualityDecision spec :=
  _root_.Hypostructure.CT16.CodeEqualityDecision.unitCost
    codeComputationBudget.size (by
      intro _previous
      change DecidableEq Bool
      infer_instance)

def coordinateQuery : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Coordinate previous) :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual)).map
      fun _previous residual => residual.coordinates

def capability : _root_.Hypostructure.CT16.Capability spec where
  coordinates := coordinateQuery
  inSupportDecidable := by
    intro previous coordinate
    cases mode : (Core.Residual.residualOf previous).mode <;>
      simp [spec, inSupport, mode] <;> infer_instance
  codeComputation := codeComputation
  equalityDecision := equalityDecision

def previous (mode : Mode) : Previous :=
  Core.Residual.Ledger.initial ⟨mode, coordinateSchedule⟩

def properGeneration :=
  _root_.Hypostructure.CT16.generateCounted spec capability (previous .proper)

def exactGeneration :=
  _root_.Hypostructure.CT16.generateCounted spec capability (previous .exact)

def mismatchGeneration :=
  _root_.Hypostructure.CT16.generateCounted spec capability (previous .mismatch)

theorem proper_terminal :
    properGeneration.value.terminal = .properSupport :=
  rfl

theorem exact_terminal :
    exactGeneration.value.terminal = .exactCode :=
  rfl

theorem mismatch_terminal :
    mismatchGeneration.value.terminal = .mismatch :=
  rfl

theorem proper_trace_exact :
    properGeneration.value.traceNodes =
      [.entry, .coordinateSchedule, .supportScan, .properSupportTerminal] :=
  rfl

theorem exact_trace_exact :
    exactGeneration.value.traceNodes =
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .exactCodeTerminal] :=
  rfl

theorem mismatch_trace_exact :
    mismatchGeneration.value.traceNodes =
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .mismatchTerminal] :=
  rfl

theorem proper_checks_exact : properGeneration.checks = 2 :=
  rfl

theorem exact_checks_exact : exactGeneration.checks = 6 :=
  rfl

theorem mismatch_checks_exact : mismatchGeneration.checks = 7 :=
  rfl

theorem proper_component_checks :
    properGeneration.value.supportChecks = 2 ∧
      properGeneration.value.codeChecks = 0 ∧
      properGeneration.value.equalityChecks = 0 := by
  decide

theorem exact_component_checks :
    exactGeneration.value.supportChecks = 3 ∧
      exactGeneration.value.codeChecks = 2 ∧
      exactGeneration.value.equalityChecks = 1 := by
  decide

theorem mismatch_component_checks :
    mismatchGeneration.value.supportChecks = 3 ∧
      mismatchGeneration.value.codeChecks = 3 ∧
      mismatchGeneration.value.equalityChecks = 1 := by
  decide

theorem exact_checks_match_canonical_execution :
    exactGeneration.checks =
      Core.Finite.Accounting.executionChecks
          (_root_.Hypostructure.CT16.supportScan spec capability
            (previous .exact)) +
        _root_.Hypostructure.CT16.terminalSuffixChecks capability
          (previous .exact)
          exactGeneration.value.terminal :=
  _root_.Hypostructure.CT16.generateCounted_checks
    spec capability (previous .exact)

theorem mismatch_checks_match_predecessor_budget :
    mismatchGeneration.checks =
      (_root_.Hypostructure.CT16.generationBudget spec capability).checks
        (previous .mismatch) :=
  _root_.Hypostructure.CT16.generateCounted_checks_eq_budget
    spec capability (previous .mismatch)

theorem proper_work_uses_exact_schedule :
    properGeneration.checks ≤
      capability.worstCaseChecks (previous .proper) :=
  _root_.Hypostructure.CT16.generateCounted_checks_le_worstCase
    spec capability (previous .proper)

theorem exact_work_is_polynomial :
    exactGeneration.checks ≤
      (_root_.Hypostructure.CT16.generationBudget
        spec capability).coefficient *
        ((_root_.Hypostructure.CT16.generationBudget
          spec capability).size (previous .exact) + 1) ^
        (_root_.Hypostructure.CT16.generationBudget
          spec capability).degree :=
  _root_.Hypostructure.CT16.generateCounted_checks_le_polynomial
    spec capability (previous .exact)

def properOutput :
    _root_.Hypostructure.CT16.ProperSupportOutput
      capability (previous .proper) :=
  properGeneration.value.properSupportResidual proper_terminal

theorem proper_output_is_first_missing :
    properOutput.residual.index.1 = 1 :=
  rfl

theorem proper_output_is_absent :
    Not (spec.InSupport (previous .proper) properOutput.residual.value) :=
  properOutput.residual.absent

theorem proper_output_prefix_is_present :
    forall coordinate,
      coordinate ∈ (capability.coordinatesAt (previous .proper)).values.take
        properOutput.residual.index.1 ->
      spec.InSupport (previous .proper) coordinate :=
  properOutput.residual.beforePresent

def exactOutput : _root_.Hypostructure.CT16.ExactCodeOutput
    capability (previous .exact) :=
  exactGeneration.value.exactCodeCertificate exact_terminal

theorem exact_output_proves_closed_type :
    _root_.Hypostructure.CT16.ExactClosedType spec (previous .exact)
      (capability.coordinatesAt (previous .exact)) :=
  ⟨exactOutput.certificate.state.whole.covers,
    exactOutput.certificate.state.exact.symm.trans
      exactOutput.certificate.equal⟩

def mismatchOutput : _root_.Hypostructure.CT16.MismatchOutput
    capability (previous .mismatch) :=
  mismatchGeneration.value.closedTypeMismatchResidual mismatch_terminal

theorem mismatch_output_proves_exact_complement :
    _root_.Hypostructure.CT16.WholeSupport spec (previous .mismatch)
        (capability.coordinatesAt (previous .mismatch)) ∧
      spec.closedCode (previous .mismatch) ≠
        spec.targetCode (previous .mismatch) := by
  refine ⟨mismatchOutput.residual.state.whole.covers, ?_⟩
  intro equal
  exact mismatchOutput.residual.notEqual
    (mismatchOutput.residual.state.exact.trans equal)

/-- A downstream executor can embed the output without adding an intermediate
decision stage or changing the literal predecessor. -/
abbrev EmbeddedStage := Core.Residual.Ledger.Extension Previous fun previous =>
  _root_.Hypostructure.CT16.Generated spec capability previous

def embedCounted (incoming : Previous) : Core.Counted EmbeddedStage :=
  (_root_.Hypostructure.CT16.generateCounted spec capability incoming).map
    (Core.Residual.Ledger.extend incoming)

theorem embedded_previous_is_literal :
    (embedCounted (previous .proper)).value.previous = previous .proper :=
  rfl

theorem embedding_preserves_exact_checks :
    (embedCounted (previous .proper)).checks = properGeneration.checks :=
  rfl

def stagedRun :=
  _root_.Hypostructure.CT16.run spec capability (previous .exact)

theorem run_delegates_to_generated_payload :
    stagedRun.stage.added = exactGeneration.value :=
  rfl

theorem run_retains_literal_predecessor :
    stagedRun.stage.previous = previous .exact :=
  _root_.Hypostructure.CT16.run_previous spec capability (previous .exact)

#print axioms _root_.Hypostructure.CT16.generateCounted
#print axioms _root_.Hypostructure.CT16.generateCounted_checks
#print axioms _root_.Hypostructure.CT16.generateCounted_checks_le_polynomial
#print axioms proper_output_is_first_missing
#print axioms exact_output_proves_closed_type
#print axioms mismatch_output_proves_exact_complement

end Hypostructure.Fixtures.CT16Generated
