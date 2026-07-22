import Hypostructure.CT7.Search

/-!
# CT7 output-only counted execution

The realization scan is evaluated once.  Its retained execution is routed by
Core.  Only its exhaustive branch evaluates and routes one retained response-
distinction scan.  The output-only generator composes the actual `Counted`
computations and CT7 appends exactly that sealed payload to the literal
predecessor.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue uSearch

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
    Previous}

/-- Exhaustive CT7 terminals. -/
inductive Terminal where
  | realization
  | distinguishing
  | neutral
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT7 reference flow. -/
inductive NodeId where
  | entry
  | contextSchedule
  | realizationSearch
  | distinctionSearch
  | realizationTerminal
  | distinguishingTerminal
  | neutralTerminal
  deriving DecidableEq, Repr

/-- Terminal-indexed framework evidence. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | realization (certificate : RealizationCertificate capability previous) :
      Outcome capability previous .realization
  | distinguishing
      (residual : DistinguishingResidual capability previous) :
      Outcome capability previous .distinguishing
  | neutral (certificate : NeutralityCertificate capability previous) :
      Outcome capability previous .neutral

/-- Terminal-indexed reference traces. -/
inductive Trace : Terminal -> Type where
  | realization : Trace .realization
  | distinguishing : Trace .distinguishing
  | neutral : Trace .neutral

namespace Trace

/-- Observable nodes of a typed CT7 trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .realization, .realization =>
      [.entry, .contextSchedule, .realizationSearch, .realizationTerminal]
  | .distinguishing, .distinguishing =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .distinguishingTerminal]
  | .neutral, .neutral =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .neutralTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .realization =>
      [.entry, .contextSchedule, .realizationSearch, .realizationTerminal]
  | .distinguishing =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .distinguishingTerminal]
  | .neutral =>
      [.entry, .contextSchedule, .realizationSearch, .distinctionSearch,
        .neutralTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .realization, .realization => rfl
  | .distinguishing, .distinguishing => rfl
  | .neutral, .neutral => rfl

end Trace

/-- Unique typed trace selected from generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | realization _ => exact .realization
  | distinguishing _ => exact .distinguishing
  | neutral _ => exact .neutral

/-- Exact primitive checks charged by each generated path. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .realization, .realization certificate => certificate.index.1 + 1
  | .distinguishing, .distinguishing residual =>
      (capability.contextsAt previous).card +
        (residual.distinction.index.1 + 1)
  | .neutral, .neutral _ =>
      localCheckBound (capability.contextsAt previous)

/-- Exact charged work is bounded by the two complete residual-owned passes. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <= localCheckBound
      (capability.contextsAt previous) := by
  cases outcome with
  | realization certificate =>
      have inspected : certificate.index.1 + 1 <=
          (capability.contextsAt previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | distinguishing residual =>
      have inspected : residual.distinction.index.1 + 1 <=
          (capability.contextsAt previous).card :=
        Nat.succ_le_iff.mpr residual.distinction.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | neutral _ =>
      rfl

/-- Recover the exact first hit and its defining execution equation from
Core's generated hit branch. -/
private def hitWithExecutionEquation
    {alpha : Type uSearch} {schedule : Core.Finite.Enumeration alpha}
    {predicate : alpha -> Prop}
    (execution : Core.Finite.Search.Execution schedule predicate)
    (hasHit : execution.HasHit) :
    { hit : Core.Finite.Search.IndexedHit schedule predicate //
      execution.hit? = some hit } := by
  cases found : execution.hit? with
  | none =>
      simp [Core.Finite.Search.Execution.HasHit, found] at hasHit
  | some hit =>
      exact ⟨hit, rfl⟩

/-- An execution whose exact schedule is avoided charges the complete schedule. -/
private theorem executionChecks_eq_card_of_avoidance
    {alpha : Type uSearch} {schedule : Core.Finite.Enumeration alpha}
    {predicate : alpha -> Prop}
    (execution : Core.Finite.Search.Execution schedule predicate)
    (avoidance : Core.Finite.Search.Avoids schedule predicate) :
    Core.Finite.Accounting.executionChecks execution = schedule.card := by
  cases found : execution.hit? with
  | none =>
      exact Core.Finite.Accounting.executionChecks_of_miss execution found
  | some hit =>
      exact (avoidance hit.index hit.sound).elim

/-- Constructor-sealed output-only CT7 generation indexed by the literal
predecessor.  It retains the exact first execution and, precisely on the two
exhaustive-first-scan terminals, the exact second execution. -/
structure Generated (capability : Capability spec) (previous : Previous) where
  private mk ::
  realizationExecution : Core.Finite.Search.Execution
    (capability.contextsAt previous) (ScheduledRealizes capability previous)
  realizationExecution_eq : realizationExecution =
    (countedRealizationScan capability previous).value
  terminal : Terminal
  outcome : Outcome capability previous terminal
  trace : Trace terminal
  distinctionExecution : Option (Core.Finite.Search.Execution
    (capability.contextsAt previous) (ResponseMismatch capability previous))
  distinctionExecution_eq : distinctionExecution =
    match terminal with
    | .realization => none
    | .distinguishing | .neutral =>
        some (countedDistinctionScan capability previous).value
  realizationChecks : Nat
  realizationChecks_eq : realizationChecks =
    Core.Finite.Accounting.executionChecks realizationExecution
  distinctionChecks : Nat
  distinctionChecks_eq : distinctionChecks =
    match terminal with
    | .realization => 0
    | .distinguishing | .neutral =>
        (countedDistinctionScan capability previous).checks
  checks : Nat
  checks_eq : checks = realizationChecks + distinctionChecks
  checks_eq_outcomeChecks : checks = outcomeChecks outcome

/-- Run CT7 without extending the incoming ledger.  `Counted.bind` charges the
one realization scan.  Only its exhaustive branch constructs the second
`Counted` scan, whose actual count is composed by `Counted.map`. -/
private def generate (capability : Capability spec) (previous : Previous) :
    Core.Counted (Generated capability previous) :=
  let realizationResult := countedRealizationScan capability previous
  realizationResult.bind fun _ =>
    let realizationExecution := realizationResult.value
    let routedRealization :=
      routeRealizationExecution capability previous realizationExecution
    match routedRealization.added with
    | .yesBranch hasRealization =>
        let selected := hitWithExecutionEquation
          routedRealization.previous hasRealization
        let certificate := selected.1
        let generated : Generated capability previous := {
          realizationExecution := realizationExecution
          realizationExecution_eq := rfl
          terminal := .realization
          outcome := .realization certificate
          trace := .realization
          distinctionExecution := none
          distinctionExecution_eq := rfl
          realizationChecks := realizationResult.checks
          realizationChecks_eq := rfl
          distinctionChecks := 0
          distinctionChecks_eq := rfl
          checks := realizationResult.checks
          checks_eq := by omega
          checks_eq_outcomeChecks := by
            have exactChecks : realizationResult.checks =
                certificate.index.1 + 1 := by
              calc
                realizationResult.checks =
                    Core.Finite.Accounting.executionChecks
                      realizationExecution := rfl
                _ = certificate.index.1 + 1 :=
                  Core.Finite.Accounting.executionChecks_of_hit
                    realizationExecution certificate selected.2
            simpa only [outcomeChecks] using exactChecks
        }
        Core.Counted.pure generated
    | .noBranch unrealized =>
        let distinctionResult := countedDistinctionScan capability previous
        distinctionResult.map fun _ =>
          let distinctionExecution := distinctionResult.value
          let routedDistinction :=
            routeDistinctionExecution capability previous distinctionExecution
          match routedDistinction.added with
          | .yesBranch hasDistinction =>
              let selected := hitWithExecutionEquation
                routedDistinction.previous hasDistinction
              let residual := DistinguishingResidual.ofHit unrealized
                selected.1
              let generated : Generated capability previous := {
                realizationExecution := realizationExecution
                realizationExecution_eq := rfl
                terminal := .distinguishing
                outcome := .distinguishing residual
                trace := .distinguishing
                distinctionExecution := some distinctionExecution
                distinctionExecution_eq := rfl
                realizationChecks := realizationResult.checks
                realizationChecks_eq := rfl
                distinctionChecks := distinctionResult.checks
                distinctionChecks_eq := rfl
                checks := realizationResult.checks + distinctionResult.checks
                checks_eq := rfl
                checks_eq_outcomeChecks := by
                  have realizationExact : realizationResult.checks =
                      (capability.contextsAt previous).card := by
                    calc
                      realizationResult.checks =
                          Core.Finite.Accounting.executionChecks
                            realizationExecution := rfl
                      _ = (capability.contextsAt previous).card :=
                        executionChecks_eq_card_of_avoidance
                          realizationExecution unrealized
                  have distinctionExact : distinctionResult.checks =
                      selected.1.index.1 + 1 := by
                    calc
                      distinctionResult.checks =
                          Core.Finite.Accounting.executionChecks
                            distinctionExecution := rfl
                      _ = selected.1.index.1 + 1 :=
                        Core.Finite.Accounting.executionChecks_of_hit
                          distinctionExecution selected.1 selected.2
                  change realizationResult.checks + distinctionResult.checks =
                    (capability.contextsAt previous).card +
                      (selected.1.index.1 + 1)
                  omega
              }
              generated
          | .noBranch neutral =>
              let certificate :=
                NeutralityCertificate.ofAvoidance unrealized neutral
              let generated : Generated capability previous := {
                realizationExecution := realizationExecution
                realizationExecution_eq := rfl
                terminal := .neutral
                outcome := .neutral certificate
                trace := .neutral
                distinctionExecution := some distinctionExecution
                distinctionExecution_eq := rfl
                realizationChecks := realizationResult.checks
                realizationChecks_eq := rfl
                distinctionChecks := distinctionResult.checks
                distinctionChecks_eq := rfl
                checks := realizationResult.checks + distinctionResult.checks
                checks_eq := rfl
                checks_eq_outcomeChecks := by
                  have realizationExact : realizationResult.checks =
                      (capability.contextsAt previous).card := by
                    calc
                      realizationResult.checks =
                          Core.Finite.Accounting.executionChecks
                            realizationExecution := rfl
                      _ = (capability.contextsAt previous).card :=
                        executionChecks_eq_card_of_avoidance
                          realizationExecution unrealized
                  have distinctionExact : distinctionResult.checks =
                      (capability.contextsAt previous).card := by
                    calc
                      distinctionResult.checks =
                          Core.Finite.Accounting.executionChecks
                            distinctionExecution := rfl
                      _ = (capability.contextsAt previous).card :=
                        executionChecks_eq_card_of_avoidance
                          distinctionExecution neutral
                  change realizationResult.checks + distinctionResult.checks =
                    localCheckBound (capability.contextsAt previous)
                  simp only [localCheckBound]
                  omega
              }
              generated

namespace Generated

variable {capability : Capability spec} {previous : Previous}

/-- Observable exact trace nodes. -/
def traceNodes (generated : Generated capability previous) : List NodeId :=
  generated.trace.nodes

/-- The retained realization execution is the one actual counted scan. -/
theorem realizationExecution_eq_countedScan
    (generated : Generated capability previous) :
    generated.realizationExecution =
      (countedRealizationScan capability previous).value :=
  generated.realizationExecution_eq

/-- The retained realization count is the count of that exact scan product. -/
theorem realizationChecks_eq_countedScan
    (generated : Generated capability previous) :
    generated.realizationChecks =
      (countedRealizationScan capability previous).checks := by
  rw [generated.realizationChecks_eq,
    generated.realizationExecution_eq_countedScan]
  rfl

/-- Realization skips the distinction scan and charges zero distinction work. -/
theorem distinctionChecks_eq_zero
    (generated : Generated capability previous)
    (isRealization : generated.terminal = .realization) :
    generated.distinctionChecks = 0 := by
  rcases generated with
    ⟨realizationExecution, realizationExecution_eq, terminal, outcome, trace,
      distinctionExecution, distinctionExecution_eq, realizationChecks,
      realizationChecks_eq, distinctionChecks, distinctionChecks_eq, checks,
      checks_eq, checks_eq_outcomeChecks⟩
  cases outcome with
  | realization _ => simpa using distinctionChecks_eq
  | distinguishing _ => cases isRealization
  | neutral _ => cases isRealization

/-- A distinguishing terminal retains and charges the one canonical second
scan. -/
theorem distinctionChecks_eq_countedScan_of_distinguishing
    (generated : Generated capability previous)
    (isDistinguishing : generated.terminal = .distinguishing) :
    generated.distinctionChecks =
      (countedDistinctionScan capability previous).checks := by
  rcases generated with
    ⟨realizationExecution, realizationExecution_eq, terminal, outcome, trace,
      distinctionExecution, distinctionExecution_eq, realizationChecks,
      realizationChecks_eq, distinctionChecks, distinctionChecks_eq, checks,
      checks_eq, checks_eq_outcomeChecks⟩
  cases outcome with
  | realization _ => cases isDistinguishing
  | distinguishing _ => simpa using distinctionChecks_eq
  | neutral _ => cases isDistinguishing

/-- A neutral terminal retains and charges the one canonical second scan. -/
theorem distinctionChecks_eq_countedScan_of_neutral
    (generated : Generated capability previous)
    (isNeutral : generated.terminal = .neutral) :
    generated.distinctionChecks =
      (countedDistinctionScan capability previous).checks := by
  rcases generated with
    ⟨realizationExecution, realizationExecution_eq, terminal, outcome, trace,
      distinctionExecution, distinctionExecution_eq, realizationChecks,
      realizationChecks_eq, distinctionChecks, distinctionChecks_eq, checks,
      checks_eq, checks_eq_outcomeChecks⟩
  cases outcome with
  | realization _ => cases isNeutral
  | distinguishing _ => cases isNeutral
  | neutral _ => simpa using distinctionChecks_eq

/-- Exact realization-terminal work is the actual first counted scan only. -/
theorem checks_eq_realization
    (generated : Generated capability previous)
    (isRealization : generated.terminal = .realization) :
    generated.checks =
      (countedRealizationScan capability previous).checks := by
  rw [generated.checks_eq, generated.realizationChecks_eq_countedScan,
    generated.distinctionChecks_eq_zero isRealization, Nat.add_zero]

/-- Exact distinguishing-terminal work composes the actual first and second
counted scans. -/
theorem checks_eq_distinguishing
    (generated : Generated capability previous)
    (isDistinguishing : generated.terminal = .distinguishing) :
    generated.checks =
      (countedRealizationScan capability previous).checks +
        (countedDistinctionScan capability previous).checks := by
  rw [generated.checks_eq, generated.realizationChecks_eq_countedScan,
    generated.distinctionChecks_eq_countedScan_of_distinguishing
      isDistinguishing]

/-- Exact neutral-terminal work composes the actual exhaustive first and second
counted scans. -/
theorem checks_eq_neutral
    (generated : Generated capability previous)
    (isNeutral : generated.terminal = .neutral) :
    generated.checks =
      (countedRealizationScan capability previous).checks +
        (countedDistinctionScan capability previous).checks := by
  rw [generated.checks_eq, generated.realizationChecks_eq_countedScan,
    generated.distinctionChecks_eq_countedScan_of_neutral isNeutral]

/-- Every generated trace is fixed by its generated terminal. -/
theorem traceNodes_eq_expected
    (generated : Generated capability previous) :
    generated.traceNodes = Trace.expectedNodes generated.terminal :=
  generated.trace.nodes_eq_expected

/-- Generated work is exactly the historical semantic terminal view. -/
theorem checks_exact (generated : Generated capability previous) :
    generated.checks = outcomeChecks generated.outcome :=
  generated.checks_eq_outcomeChecks

/-- Generated work stays inside the two complete predecessor-owned passes. -/
theorem checks_le_limit (generated : Generated capability previous) :
    generated.checks <= localCheckBound
      (capability.contextsAt previous) := by
  rw [generated.checks_exact]
  exact outcomeChecks_le_limit generated.outcome

end Generated

/-- Generate CT7's unique semantic payload without extending the literal
predecessor. -/
def generateCounted (capability : Capability spec) (previous : Previous) :
    Core.Counted (Generated capability previous) :=
  generate capability previous

@[simp] theorem generateCounted_checks_eq_value
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks =
      (generateCounted capability previous).value.checks := by
  unfold generateCounted generate
  dsimp only [Core.Counted.bind, Core.Counted.map, Core.Counted.pure]
  split
  · rfl
  · split <;> rfl

/-- Exact generated work stated through the generated semantic outcome. -/
@[simp] theorem generateCounted_checks
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks =
      outcomeChecks (generateCounted capability previous).value.outcome := by
  rw [generateCounted_checks_eq_value]
  exact (generateCounted capability previous).value.checks_exact

/-- Output-only generation stays inside the complete two-pass schedule. -/
theorem generateCounted_checks_le_limit
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks <=
      localCheckBound (capability.contextsAt previous) := by
  rw [generateCounted_checks_eq_value]
  exact (generateCounted capability previous).value.checks_le_limit

/-- Exact predecessor-indexed work budget for embedding CT7 generation in a
focused or routed framework executor. -/
def generationBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.linearWorkBudget.size
  checks := fun previous => (generateCounted capability previous).checks
  coefficient := capability.linearWorkBudget.coefficient
  degree := capability.linearWorkBudget.degree
  bounded := by
    intro previous
    exact (generateCounted_checks_le_limit capability previous).trans
      (capability.linearWorkBudget.bounded previous)

@[simp] theorem generationBudget_checks
    (capability : Capability spec) (previous : Previous) :
    (generationBudget capability).checks previous =
      (generateCounted capability previous).checks :=
  rfl

@[simp] theorem generateCounted_checks_eq_budget
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks =
      (generationBudget capability).checks previous :=
  rfl

/-- The counted generator satisfies its exact predecessor-indexed budget. -/
theorem generateCounted_checks_le_polynomial
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks <=
      (generationBudget capability).coefficient *
        ((generationBudget capability).size previous + 1) ^
          (generationBudget capability).degree :=
  (generationBudget capability).bounded previous

/-- The one accumulated CT7 stage retains the literal predecessor and the
sealed generated payload. -/
abbrev Stage
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Generated capability previous

/-- Closed CT7 execution result. -/
structure ExecutionResult
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability

namespace ExecutionResult

/-- Framework-derived terminal. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Typed semantic evidence retained in the generated ledger entry. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Exact generated trace. -/
def trace {capability : Capability spec}
    (result : ExecutionResult spec capability) : Trace result.terminal :=
  result.stage.added.trace

/-- Exact observable trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.stage.added.traceNodes

/-- Exact charged work from the actual counted generator. -/
def checks {capability : Capability spec}
    (result : ExecutionResult spec capability) : Nat :=
  result.stage.added.checks

/-- Exact charged work agrees with the generated terminal semantics. -/
theorem checks_exact {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks = outcomeChecks result.outcome :=
  result.stage.added.checks_exact

/-- Every generated path is bounded by two complete passes. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= localCheckBound
      (capability.contextsAt result.stage.previous) :=
  result.stage.added.checks_le_limit

/-- Every generated execution satisfies CT7's automatic linear envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= (capability.linearWorkBudget).coefficient *
      ((capability.linearWorkBudget).size result.stage.previous + 1) ^
        (capability.linearWorkBudget).degree :=
  result.checks_le_limit.trans
    (capability.linearWorkBudget.bounded result.stage.previous)

end ExecutionResult

/-- Execute CT7 on one literal predecessor and append the generated value. -/
def run
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let generated := generateCounted capability previous
  .mk (Core.Residual.Ledger.extend previous generated.value)

@[simp] theorem run_generated_eq
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.added =
      (generateCounted capability previous).value :=
  rfl

@[simp] theorem run_checks_eq_generated
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).checks =
      (generateCounted capability previous).checks :=
  (generateCounted_checks_eq_value capability previous).symm

@[simp] theorem run_checks_eq_generationBudget
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).checks =
      (generationBudget capability).checks previous := by
  rw [run_checks_eq_generated, generateCounted_checks_eq_budget]

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
      Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT7
