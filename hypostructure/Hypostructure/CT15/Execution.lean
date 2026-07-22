import Hypostructure.CT15.Search

/-!
# CT15 accumulated execution

Core finite search and Core binary decisions select every branch.  CT15 stores
the generated terminal-indexed evidence as one extension of the literal
incoming ledger.  Both the routed value and the public execution result have
private constructors.
-/

namespace Hypostructure.CT15

universe uPrevious uCoordinate

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uCoordinate} Previous}

/-- Exhaustive CT15 terminals. -/
inductive Terminal where
  | rankDrop
  | c4
  | fullRankLedger
  deriving DecidableEq, Repr

/-- Audit nodes in the complete CT15 reference flow. -/
inductive NodeId where
  | entry
  | rankComputation
  | firstDropSearch
  | ledgerComputation
  | capacityComparison
  | rankDropTerminal
  | c4Terminal
  | fullRankLedgerTerminal
  deriving DecidableEq, Repr

/-- Framework-generated branch evidence, indexed by the selected terminal. -/
inductive Outcome (capability : Capability spec) (previous : Previous) :
    Terminal -> Type _ where
  | rankDrop (rank : RankState capability previous)
      (certificate : RankDropCertificate capability previous) :
      Outcome capability previous .rankDrop
  | c4 (rank : RankState capability previous)
      (full : FullRankState capability previous rank)
      (ledger : ChargeLedger capability previous full)
      (certificate : C4Certificate capability previous ledger) :
      Outcome capability previous .c4
  | fullRankLedger (rank : RankState capability previous)
      (full : FullRankState capability previous rank)
      (ledger : ChargeLedger capability previous full)
      (residual : FullRankLedgerResidual capability previous ledger) :
      Outcome capability previous .fullRankLedger

/-- Terminal-indexed CT15 trace. -/
inductive Trace : Terminal -> Type where
  | rankDrop : Trace .rankDrop
  | c4 : Trace .c4
  | fullRankLedger : Trace .fullRankLedger

namespace Trace

/-- Observable node sequence of a typed trace. -/
def nodes : {terminal : Terminal} -> Trace terminal -> List NodeId
  | .rankDrop, .rankDrop =>
      [.entry, .rankComputation, .firstDropSearch, .rankDropTerminal]
  | .c4, .c4 =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .c4Terminal]
  | .fullRankLedger, .fullRankLedger =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .fullRankLedgerTerminal]

/-- Canonical node sequence fixed by a semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .rankDrop =>
      [.entry, .rankComputation, .firstDropSearch, .rankDropTerminal]
  | .c4 =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .c4Terminal]
  | .fullRankLedger =>
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .fullRankLedgerTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace terminal) -> trace.nodes = expectedNodes terminal
  | .rankDrop, .rankDrop => rfl
  | .c4, .c4 => rfl
  | .fullRankLedger, .fullRankLedger => rfl

end Trace

/-- CT15-routed evidence.  Its private constructor prevents callers from
selecting a terminal or installing unrelated branch evidence. -/
structure Routed (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome capability previous terminal

/-- Unique typed trace selected by generated outcome evidence. -/
def traceOfOutcome {capability : Capability spec} {previous : Previous}
    {terminal : Terminal} (outcome : Outcome capability previous terminal) :
    Trace terminal := by
  cases outcome with
  | rankDrop _ _ => exact .rankDrop
  | c4 _ _ _ _ => exact .c4
  | fullRankLedger _ _ _ _ => exact .fullRankLedger

/-- Unique typed trace selected by the private routed result. -/
def traceOfRouted {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfOutcome routed.outcome

/-- Exact primitive decisions charged by each terminal.

The rank pass inspects every coordinate.  A drop then pays exactly its first
hit prefix.  A full-rank outcome pays the exhaustive second pass and one
capacity comparison.  Pure charge evaluation is mathematical data
construction, not a predicate decision. -/
def outcomeChecks {capability : Capability spec} {previous : Previous} :
    {terminal : Terminal} -> Outcome capability previous terminal -> Nat
  | .rankDrop, .rankDrop _ certificate =>
      (capability.coordinatesAt previous).card + certificate.index.1 + 1
  | .c4, .c4 _ _ _ _ =>
      localCheckBound (capability.coordinatesAt previous)
  | .fullRankLedger, .fullRankLedger _ _ _ _ =>
      localCheckBound (capability.coordinatesAt previous)

/-- Branch-exact work never exceeds the complete prescribed schedule. -/
theorem outcomeChecks_le_limit {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal) :
    outcomeChecks outcome <=
      localCheckBound (capability.coordinatesAt previous) := by
  cases outcome with
  | rankDrop _ certificate =>
      have inspected : certificate.index.1 + 1 <=
          (capability.coordinatesAt previous).card :=
        Nat.succ_le_iff.mpr certificate.index.isLt
      simp only [outcomeChecks, localCheckBound]
      omega
  | c4 _ _ _ _ => rfl
  | fullRankLedger _ _ _ _ => rfl

/-- Private executor package retaining the proof that its operational count
agrees with the established terminal-indexed accounting view. -/
private structure CountedReferenceResult (capability : Capability spec)
    (previous : Previous) where
  counted : Core.Counted (Routed capability previous)
  checks_eq : counted.checks = outcomeChecks counted.value.outcome

/-- Counted reference execution.  The canonical counted first-drop scan and,
on the exhaustive branch, the counted capacity comparison are each evaluated
once.  Their exact routed values select the semantic terminal and their stored
counts are accumulated with the mandatory complete rank pass. -/
private def executeReference (capability : Capability spec)
    (previous : Previous) : CountedReferenceResult capability previous :=
  let rank := computeRank capability previous
  let rankPassChecks := (capability.coordinatesAt previous).card
  let scan := countedDropScan capability previous
  let dropped := Core.Finite.Search.route scan.value
  match dropped.added with
  | .yesBranch hasDrop =>
      {
        counted := ⟨.mk .rankDrop (.rankDrop rank
          (scan.value.hitOfHasHit hasDrop)),
          rankPassChecks + scan.checks⟩
        checks_eq := by
          have scanChecks : scan.checks =
              (scan.value.hitOfHasHit hasDrop).index.1 + 1 :=
            countedDropScan_checks_eq_hit capability previous hasDrop
          simp only [outcomeChecks]
          omega
      }
  | .noBranch independence =>
      let full := fullRankOfIndependence capability previous rank independence
      let ledger := buildLedger capability previous full
      let comparison := countedCompareLedger capability previous ledger
      match comparison.value.added with
      | .yesBranch exceeded =>
          {
            counted := ⟨.mk .c4 (.c4 rank full ledger (by
              have exactExceeded := exceeded
              rw [show comparison.value.previous = ledger from rfl]
                at exactExceeded
              exact exactExceeded)),
              rankPassChecks + scan.checks + comparison.checks⟩
            checks_eq := by
              have scanChecks : scan.checks = rankPassChecks :=
                countedDropScan_checks_eq_card_of_independence
                  capability previous independence
              have comparisonChecks : comparison.checks = 1 :=
                countedCompareLedger_checks capability previous ledger
              simp only [outcomeChecks, localCheckBound]
              omega
          }
      | .noBranch available =>
          {
            counted := ⟨.mk .fullRankLedger
              (.fullRankLedger rank full ledger (by
                have exactAvailable := available
                rw [show comparison.value.previous = ledger from rfl]
                  at exactAvailable
                exact exactAvailable)),
              rankPassChecks + scan.checks + comparison.checks⟩
            checks_eq := by
              have scanChecks : scan.checks = rankPassChecks :=
                countedDropScan_checks_eq_card_of_independence
                  capability previous independence
              have comparisonChecks : comparison.checks = 1 :=
                countedCompareLedger_checks capability previous ledger
              simp only [outcomeChecks, localCheckBound]
              omega
          }

/-- The counted result projected from the single private reference
execution. -/
private def countedRouteReference (capability : Capability spec)
    (previous : Previous) : Core.Counted (Routed capability previous) :=
  (executeReference capability previous).counted

/-- Core routes first-drop and capacity decisions; CT15 exposes the semantic
value of the counted reference execution without rerunning either decision. -/
def routeReference (capability : Capability spec) (previous : Previous) :
    Routed capability previous :=
  (countedRouteReference capability previous).value

/-- Terminal-refined rank-drop output.  Its private constructor prevents
callers from manufacturing branch evidence independently of CT15 routing. -/
structure RankDropOutput (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  rank : RankState capability previous
  certificate : RankDropCertificate capability previous

/-- Terminal-refined C4 output with the exact generated full-rank ledger. -/
structure C4Output (capability : Capability spec) (previous : Previous) where
  private mk ::
  rank : RankState capability previous
  full : FullRankState capability previous rank
  ledger : ChargeLedger capability previous full
  certificate : C4Certificate capability previous ledger

/-- Terminal-refined capacity-fitting full-rank output. -/
structure FullRankLedgerOutput (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  rank : RankState capability previous
  full : FullRankState capability previous rank
  ledger : ChargeLedger capability previous full
  residual : FullRankLedgerResidual capability previous ledger

namespace Routed

/-- Exact terminal-indexed trace selected by one routed output. -/
def trace {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Trace routed.terminal :=
  traceOfRouted routed

/-- Observable trace nodes of one output-only routed value. -/
def traceNodes {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : List NodeId :=
  routed.trace.nodes

/-- Exact primitive checks charged to one routed outcome. -/
def checks {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) : Nat :=
  outcomeChecks routed.outcome

@[simp] theorem checks_eq_outcomeChecks {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous) :
    routed.checks = outcomeChecks routed.outcome :=
  rfl

theorem traceNodes_eq_expected {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous) :
    routed.traceNodes = Trace.expectedNodes routed.terminal :=
  Trace.nodes_eq_expected routed.trace

/-- Recover rank-drop evidence only after the generated terminal proves that
this is the rank-drop branch. -/
def rankDropOutput {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isRankDrop : routed.terminal = .rankDrop) :
    RankDropOutput capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | rankDrop rank certificate => exact ⟨rank, certificate⟩
  | c4 _ _ _ _ => cases isRankDrop
  | fullRankLedger _ _ _ _ => cases isRankDrop

/-- Recover C4 evidence only from the generated overload terminal. -/
def c4Output {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) (isC4 : routed.terminal = .c4) :
    C4Output capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | rankDrop _ _ => cases isC4
  | c4 rank full ledger certificate =>
      exact ⟨rank, full, ledger, certificate⟩
  | fullRankLedger _ _ _ _ => cases isC4

/-- Recover the capacity-fitting full-rank ledger only from its generated
terminal. -/
def fullRankLedgerOutput {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isFullRankLedger : routed.terminal = .fullRankLedger) :
    FullRankLedgerOutput capability previous := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | rankDrop _ _ => cases isFullRankLedger
  | c4 _ _ _ _ => cases isFullRankLedger
  | fullRankLedger rank full ledger residual =>
      exact ⟨rank, full, ledger, residual⟩

/-- Rank-drop work is exactly the full rank pass plus the first-hit prefix. -/
theorem checks_eq_rankDrop {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isRankDrop : routed.terminal = .rankDrop) :
    routed.checks = (capability.coordinatesAt previous).card +
      (routed.rankDropOutput isRankDrop).certificate.index.1 + 1 := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | rankDrop _ _ => rfl
  | c4 _ _ _ _ => cases isRankDrop
  | fullRankLedger _ _ _ _ => cases isRankDrop

/-- C4 work is exactly the complete prescribed CT15 schedule. -/
theorem checks_eq_c4 {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous)
    (isC4 : routed.terminal = .c4) :
    routed.checks = localCheckBound (capability.coordinatesAt previous) := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | rankDrop _ _ => cases isC4
  | c4 _ _ _ _ => rfl
  | fullRankLedger _ _ _ _ => cases isC4

/-- Capacity-fitting full-rank work is exactly the complete prescribed CT15
schedule. -/
theorem checks_eq_fullRankLedger {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous)
    (isFullRankLedger : routed.terminal = .fullRankLedger) :
    routed.checks = localCheckBound (capability.coordinatesAt previous) := by
  rcases routed with ⟨terminal, outcome⟩
  cases outcome with
  | rankDrop _ _ => cases isFullRankLedger
  | c4 _ _ _ _ => cases isFullRankLedger
  | fullRankLedger _ _ _ _ => rfl

/-- Output-only routed work stays inside the complete local schedule. -/
theorem checks_le_limit {capability : Capability spec} {previous : Previous}
    (routed : Routed capability previous) :
    routed.checks <=
      localCheckBound (capability.coordinatesAt previous) :=
  outcomeChecks_le_limit routed.outcome

/-- Output-only routed work satisfies the capability's declared polynomial
envelope. -/
theorem checks_le_polynomial {capability : Capability spec}
    {previous : Previous} (routed : Routed capability previous) :
    routed.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  routed.checks_le_limit.trans (capability.workBound previous)

end Routed

/-- The execution-derived count agrees with the historical terminal view.
Unlike `outcomeChecks`, the left side is assembled from the counted scan and
the counted capacity comparison that selected this exact routed value. -/
private theorem countedRouteReference_checks_eq_outcomeChecks
    (capability : Capability spec) (previous : Previous) :
    (countedRouteReference capability previous).checks =
      outcomeChecks (countedRouteReference capability previous).value.outcome :=
  (executeReference capability previous).checks_eq

/-- Exact predecessor-indexed budget of the output-only CT15 generator. -/
def generationBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => (countedRouteReference capability previous).checks
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := fun previous => by
    rw [countedRouteReference_checks_eq_outcomeChecks]
    exact (countedRouteReference capability previous).value.checks_le_polynomial

/-- Generate CT15's uniquely routed semantic payload without extending the
incoming ledger.  The returned count is accumulated from the exact canonical
counted scan and counted capacity decision used by the reference execution. -/
def generateCounted (capability : Capability spec) (previous : Previous) :
    Core.Counted (Routed capability previous) :=
  countedRouteReference capability previous

@[simp] theorem generateCounted_value (capability : Capability spec)
    (previous : Previous) :
    (generateCounted capability previous).value =
      routeReference capability previous :=
  rfl

@[simp] theorem generateCounted_checks (capability : Capability spec)
    (previous : Previous) :
    (generateCounted capability previous).checks =
      outcomeChecks (generateCounted capability previous).value.outcome :=
  countedRouteReference_checks_eq_outcomeChecks capability previous

@[simp] theorem generateCounted_checks_eq_budget
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks =
      (generationBudget capability).checks previous :=
  rfl

/-- A generated rank-drop branch stores exactly one complete rank pass plus
the execution count of the same canonical counted drop scan. -/
theorem generateCounted_checks_eq_rankDropScan
    (capability : Capability spec) (previous : Previous)
    (isRankDrop : (generateCounted capability previous).value.terminal =
      .rankDrop) :
    (generateCounted capability previous).checks =
      (capability.coordinatesAt previous).card +
        (countedDropScan capability previous).checks := by
  let output :=
    (generateCounted capability previous).value.rankDropOutput isRankDrop
  have scanChecks : (countedDropScan capability previous).checks =
      output.certificate.index.1 + 1 :=
    countedDropScan_checks_eq_certificate capability previous
      output.certificate
  calc
    (generateCounted capability previous).checks =
        (generateCounted capability previous).value.checks :=
      generateCounted_checks capability previous
    _ = (capability.coordinatesAt previous).card +
          output.certificate.index.1 + 1 := by
      simpa [output] using
        (generateCounted capability previous).value.checks_eq_rankDrop
          isRankDrop
    _ = (capability.coordinatesAt previous).card +
          (countedDropScan capability previous).checks := by omega

/-- A generated C4 branch charges the complete canonical drop scan and the
counted capacity decision performed on its exact generated ledger. -/
theorem generateCounted_checks_eq_c4ScanCapacity
    (capability : Capability spec) (previous : Previous)
    (isC4 : (generateCounted capability previous).value.terminal = .c4) :
    (generateCounted capability previous).checks =
      (capability.coordinatesAt previous).card +
        (countedDropScan capability previous).checks +
          (countedCompareLedger capability previous
            ((generateCounted capability previous).value.c4Output
              isC4).ledger).checks := by
  let output := (generateCounted capability previous).value.c4Output isC4
  have scanChecks : (countedDropScan capability previous).checks =
      (capability.coordinatesAt previous).card :=
    countedDropScan_checks_eq_card_of_independence capability previous
      output.full.independence
  have comparisonChecks :
      (countedCompareLedger capability previous output.ledger).checks = 1 :=
    countedCompareLedger_checks capability previous output.ledger
  change (generateCounted capability previous).checks =
    (capability.coordinatesAt previous).card +
      (countedDropScan capability previous).checks +
        (countedCompareLedger capability previous output.ledger).checks
  calc
    (generateCounted capability previous).checks =
        (generateCounted capability previous).value.checks :=
      generateCounted_checks capability previous
    _ = localCheckBound (capability.coordinatesAt previous) :=
      (generateCounted capability previous).value.checks_eq_c4 isC4
    _ = (capability.coordinatesAt previous).card +
          (countedDropScan capability previous).checks +
            (countedCompareLedger capability previous output.ledger).checks := by
      simp only [localCheckBound]
      omega

/-- A generated capacity-fitting full-rank branch charges the complete
canonical drop scan and the counted capacity decision performed on its exact
generated ledger. -/
theorem generateCounted_checks_eq_fullRankScanCapacity
    (capability : Capability spec) (previous : Previous)
    (isFullRank : (generateCounted capability previous).value.terminal =
      .fullRankLedger) :
    (generateCounted capability previous).checks =
      (capability.coordinatesAt previous).card +
        (countedDropScan capability previous).checks +
          (countedCompareLedger capability previous
            ((generateCounted capability previous).value.fullRankLedgerOutput
              isFullRank).ledger).checks := by
  let output :=
    (generateCounted capability previous).value.fullRankLedgerOutput
      isFullRank
  have scanChecks : (countedDropScan capability previous).checks =
      (capability.coordinatesAt previous).card :=
    countedDropScan_checks_eq_card_of_independence capability previous
      output.full.independence
  have comparisonChecks :
      (countedCompareLedger capability previous output.ledger).checks = 1 :=
    countedCompareLedger_checks capability previous output.ledger
  change (generateCounted capability previous).checks =
    (capability.coordinatesAt previous).card +
      (countedDropScan capability previous).checks +
        (countedCompareLedger capability previous output.ledger).checks
  calc
    (generateCounted capability previous).checks =
        (generateCounted capability previous).value.checks :=
      generateCounted_checks capability previous
    _ = localCheckBound (capability.coordinatesAt previous) :=
      (generateCounted capability previous).value.checks_eq_fullRankLedger
        isFullRank
    _ = (capability.coordinatesAt previous).card +
          (countedDropScan capability previous).checks +
            (countedCompareLedger capability previous output.ledger).checks := by
      simp only [localCheckBound]
      omega

/-- Generated branch work never exceeds the complete predecessor-owned
coordinate schedule. -/
theorem generateCounted_checks_le_limit (capability : Capability spec)
    (previous : Previous) :
    (generateCounted capability previous).checks <=
      localCheckBound (capability.coordinatesAt previous) :=
  by
    rw [generateCounted_checks]
    exact (generateCounted capability previous).value.checks_le_limit

/-- The counted generator satisfies its predecessor-indexed polynomial
budget. -/
theorem generateCounted_checks_le_polynomial
    (capability : Capability spec) (previous : Previous) :
    (generateCounted capability previous).checks <=
      (generationBudget capability).coefficient *
        ((generationBudget capability).size previous + 1) ^
          (generationBudget capability).degree :=
  (generationBudget capability).bounded previous

/-- The accumulated CT15 stage retains the literal predecessor and one
private routed framework value. -/
abbrev Stage (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) :=
  Core.Residual.Ledger.Extension Previous fun previous =>
    Routed capability previous

/-- Closed CT15 execution result. -/
structure ExecutionResult (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) where
  private mk ::
  stage : Stage spec capability
  trace : Trace stage.added.terminal
  checks : Nat
  checks_eq : checks = outcomeChecks stage.added.outcome

namespace ExecutionResult

/-- Terminal derived from retained private route evidence. -/
def terminal {capability : Capability spec}
    (result : ExecutionResult spec capability) : Terminal :=
  result.stage.added.terminal

/-- Terminal-indexed semantic output retained by the ledger extension. -/
def outcome {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    Outcome capability result.stage.previous result.terminal :=
  result.stage.added.outcome

/-- Observable exact trace. -/
def traceNodes {capability : Capability spec}
    (result : ExecutionResult spec capability) : List NodeId :=
  result.trace.nodes

/-- Actual branch work is bounded by the complete CT15 schedule. -/
theorem checks_le_limit {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <=
      localCheckBound (capability.coordinatesAt result.stage.previous) := by
  rw [result.checks_eq]
  exact outcomeChecks_le_limit result.stage.added.outcome

/-- Every execution satisfies the capability's declared polynomial bound. -/
theorem checks_le_polynomial {capability : Capability spec}
    (result : ExecutionResult spec capability) :
    result.checks <= capability.workCoefficient *
      (capability.inputSize result.stage.previous + 1) ^
        capability.workDegree :=
  result.checks_le_limit.trans (capability.workBound result.stage.previous)

end ExecutionResult

/-- Execute CT15 on one literal incoming accumulated ledger. -/
def run (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    ExecutionResult spec capability :=
  let generated := generateCounted capability previous
  {
    stage := Core.Residual.Ledger.extend previous generated.value
    trace := generated.value.trace
    checks := generated.checks
    checks_eq := generateCounted_checks capability previous
  }

@[simp] theorem run_routed_eq_generated
    (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.added =
      (generateCounted capability previous).value :=
  rfl

@[simp] theorem run_checks_eq_generated
    (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).checks =
      (generateCounted capability previous).checks :=
  rfl

@[simp] theorem run_previous
    (spec : Spec.{uPrevious, uCoordinate} Previous)
    (capability : Capability spec) (previous : Previous) :
    (run spec capability previous).stage.previous = previous :=
  rfl

end Hypostructure.CT15
