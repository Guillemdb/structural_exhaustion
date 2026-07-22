import Hypostructure.CT15.Execution

/-!
# CT15 output-only counted generation fixture

One predecessor-owned coordinate schedule exercises rank drop, C4 overload,
and a capacity-fitting full-rank ledger.  The fixture checks exact counts,
terminal-refined outputs, the predecessor-indexed budget, and compatibility
with the accumulated executor.
-/

namespace Hypostructure.Fixtures.CT15Generated

open Hypostructure

structure Residual where
  coordinates : Core.Finite.Enumeration (Fin 3)
  dropIndex : Option (Fin 3)
  capacity : Nat

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def coordinatesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.coordinates

abbrev spec : CT15.Spec Previous where
  Coordinate := fun _previous => Fin 3
  TargetDependent := fun previous coordinate =>
    (residualQuery.read previous).dropIndex = some coordinate
  charge := fun _previous coordinate => coordinate.1 + 1
  capacity := fun previous => (residualQuery.read previous).capacity

def capability : CT15.Capability spec where
  coordinates := coordinatesQuery
  targetDependentDecidable := fun previous coordinate => by
    exact decEq (residualQuery.read previous).dropIndex (some coordinate)
  inputSize := fun previous => (coordinatesQuery.read previous).card
  workCoefficient := 2
  workDegree := 1
  workBound := by
    intro previous
    simp only [CT15.localCheckBound, Nat.pow_one]
    omega

def coordinates : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def rankDropPrevious : Previous :=
  Core.Residual.Ledger.initial {
    coordinates := coordinates
    dropIndex := some 1
    capacity := 6
  }

def c4Previous : Previous :=
  Core.Residual.Ledger.initial {
    coordinates := coordinates
    dropIndex := none
    capacity := 5
  }

def fullRankPrevious : Previous :=
  Core.Residual.Ledger.initial {
    coordinates := coordinates
    dropIndex := none
    capacity := 6
  }

def rankDropGenerated := CT15.generateCounted capability rankDropPrevious
def c4Generated := CT15.generateCounted capability c4Previous
def fullRankGenerated := CT15.generateCounted capability fullRankPrevious

def rankDropScan := CT15.countedDropScan capability rankDropPrevious
def c4Scan := CT15.countedDropScan capability c4Previous
def fullRankScan := CT15.countedDropScan capability fullRankPrevious

theorem rankDrop_terminal : rankDropGenerated.value.terminal = .rankDrop := by
  decide

theorem c4_terminal : c4Generated.value.terminal = .c4 := by
  decide

theorem fullRank_terminal :
    fullRankGenerated.value.terminal = .fullRankLedger := by
  decide

def rankDropOutput : CT15.RankDropOutput capability rankDropPrevious :=
  rankDropGenerated.value.rankDropOutput rankDrop_terminal

def c4Output : CT15.C4Output capability c4Previous :=
  c4Generated.value.c4Output c4_terminal

def fullRankOutput : CT15.FullRankLedgerOutput capability fullRankPrevious :=
  fullRankGenerated.value.fullRankLedgerOutput fullRank_terminal

def c4CapacityDecision :=
  CT15.countedCompareLedger capability c4Previous c4Output.ledger

def fullRankCapacityDecision :=
  CT15.countedCompareLedger capability fullRankPrevious fullRankOutput.ledger

theorem rankDrop_index : rankDropOutput.certificate.index.1 = 1 := by
  decide

theorem rankDrop_rank : rankDropOutput.rank.value = 2 := by
  decide

theorem c4_entries : c4Output.ledger.entries = [(0, 1), (1, 2), (2, 3)] :=
  rfl

theorem c4_total : c4Output.ledger.total = 6 := rfl

theorem c4_overload : spec.capacity c4Previous < c4Output.ledger.total :=
  c4Output.certificate

theorem fullRank_entries :
    fullRankOutput.ledger.entries = [(0, 1), (1, 2), (2, 3)] :=
  rfl

theorem fullRank_total : fullRankOutput.ledger.total = 6 := rfl

theorem fullRank_fits :
    fullRankOutput.ledger.total <= spec.capacity fullRankPrevious :=
  fullRankOutput.residual

theorem rankDrop_scan_exact_checks : rankDropScan.checks = 2 := by decide

theorem c4_scan_exhaustive_checks : c4Scan.checks = 3 := by decide

theorem fullRank_scan_exhaustive_checks : fullRankScan.checks = 3 := by decide

theorem c4_capacity_decision_checks : c4CapacityDecision.checks = 1 := rfl

theorem fullRank_capacity_decision_checks :
    fullRankCapacityDecision.checks = 1 := rfl

theorem rankDrop_checks_from_actual_scan :
    rankDropGenerated.checks =
      (capability.coordinatesAt rankDropPrevious).card +
        rankDropScan.checks :=
  CT15.generateCounted_checks_eq_rankDropScan capability rankDropPrevious
    rankDrop_terminal

theorem c4_checks_from_actual_scan_and_capacity :
    c4Generated.checks =
      (capability.coordinatesAt c4Previous).card + c4Scan.checks +
        c4CapacityDecision.checks :=
  CT15.generateCounted_checks_eq_c4ScanCapacity capability c4Previous
    c4_terminal

theorem fullRank_checks_from_actual_scan_and_capacity :
    fullRankGenerated.checks =
      (capability.coordinatesAt fullRankPrevious).card +
        fullRankScan.checks + fullRankCapacityDecision.checks :=
  CT15.generateCounted_checks_eq_fullRankScanCapacity capability
    fullRankPrevious fullRank_terminal

theorem rankDrop_exact_checks : rankDropGenerated.checks = 5 := by
  decide

theorem c4_exact_checks : c4Generated.checks = 7 := rfl

theorem fullRank_exact_checks : fullRankGenerated.checks = 7 := rfl

theorem rankDrop_checks_from_terminal :
    rankDropGenerated.value.checks =
      (capability.coordinatesAt rankDropPrevious).card +
        rankDropOutput.certificate.index.1 + 1 :=
  rankDropGenerated.value.checks_eq_rankDrop rankDrop_terminal

theorem c4_checks_from_terminal :
    c4Generated.value.checks =
      CT15.localCheckBound (capability.coordinatesAt c4Previous) :=
  c4Generated.value.checks_eq_c4 c4_terminal

theorem fullRank_checks_from_terminal :
    fullRankGenerated.value.checks =
      CT15.localCheckBound (capability.coordinatesAt fullRankPrevious) :=
  fullRankGenerated.value.checks_eq_fullRankLedger fullRank_terminal

theorem rankDrop_budget_exact :
    rankDropGenerated.checks =
      (CT15.generationBudget capability).checks rankDropPrevious :=
  CT15.generateCounted_checks_eq_budget capability rankDropPrevious

theorem c4_budget_exact :
    c4Generated.checks =
      (CT15.generationBudget capability).checks c4Previous :=
  CT15.generateCounted_checks_eq_budget capability c4Previous

theorem fullRank_budget_exact :
    fullRankGenerated.checks =
      (CT15.generationBudget capability).checks fullRankPrevious :=
  CT15.generateCounted_checks_eq_budget capability fullRankPrevious

theorem rankDrop_polynomial :
    rankDropGenerated.checks <=
      (CT15.generationBudget capability).coefficient *
        ((CT15.generationBudget capability).size rankDropPrevious + 1) ^
          (CT15.generationBudget capability).degree :=
  CT15.generateCounted_checks_le_polynomial capability rankDropPrevious

theorem rankDrop_trace :
    rankDropGenerated.value.traceNodes =
      [.entry, .rankComputation, .firstDropSearch, .rankDropTerminal] := by
  decide

theorem c4_trace :
    c4Generated.value.traceNodes =
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .c4Terminal] := by
  decide

theorem fullRank_trace :
    fullRankGenerated.value.traceNodes =
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .fullRankLedgerTerminal] := by
  decide

def rankDropRun := CT15.run spec capability rankDropPrevious
def c4Run := CT15.run spec capability c4Previous
def fullRankRun := CT15.run spec capability fullRankPrevious

theorem rankDrop_run_uses_generated :
    rankDropRun.stage.added = rankDropGenerated.value :=
  CT15.run_routed_eq_generated spec capability rankDropPrevious

theorem c4_run_uses_generated : c4Run.stage.added = c4Generated.value :=
  CT15.run_routed_eq_generated spec capability c4Previous

theorem fullRank_run_uses_generated :
    fullRankRun.stage.added = fullRankGenerated.value :=
  CT15.run_routed_eq_generated spec capability fullRankPrevious

theorem rankDrop_run_retains_predecessor :
    rankDropRun.stage.previous = rankDropPrevious :=
  CT15.run_previous spec capability rankDropPrevious

theorem c4_run_retains_predecessor : c4Run.stage.previous = c4Previous :=
  CT15.run_previous spec capability c4Previous

theorem fullRank_run_retains_predecessor :
    fullRankRun.stage.previous = fullRankPrevious :=
  CT15.run_previous spec capability fullRankPrevious

#print axioms CT15.generateCounted
#print axioms CT15.generateCounted_value
#print axioms CT15.generateCounted_checks
#print axioms CT15.generateCounted_checks_eq_rankDropScan
#print axioms CT15.generateCounted_checks_eq_c4ScanCapacity
#print axioms CT15.generateCounted_checks_eq_fullRankScanCapacity
#print axioms CT15.generateCounted_checks_le_polynomial
#print axioms rankDrop_checks_from_actual_scan
#print axioms c4_checks_from_actual_scan_and_capacity
#print axioms fullRank_checks_from_actual_scan_and_capacity
#print axioms rankDropOutput
#print axioms c4Output
#print axioms fullRankOutput
#print axioms rankDrop_run_uses_generated
#print axioms fullRank_run_retains_predecessor

end Hypostructure.Fixtures.CT15Generated
