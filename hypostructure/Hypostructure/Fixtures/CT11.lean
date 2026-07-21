import Hypostructure.Graph.CT11
import Hypostructure.PDE.CT11

/-!
# CT11 vertical-slice fixtures

One three-cell residual reaches both CT11 terminals and pins the exact ordered
work.  The Graph and PDE fixtures instantiate the same machine without adding
domain-specific outcomes, routes, or ledger updates.
-/

namespace Hypostructure.Fixtures.CT11

namespace Neutral

open Hypostructure.Core

inductive Scenario where
  | admissibilityGap
  | localizedDeficit
  deriving DecidableEq, Repr

def threeCells : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def admissibleFor : Scenario -> Fin 3 -> Prop
  | .admissibilityGap, cell => cell != 1
  | .localizedDeficit, _cell => True

def admissibleForDecidable (scenario : Scenario) (cell : Fin 3) :
    Decidable (admissibleFor scenario cell) := by
  cases scenario with
  | admissibilityGap =>
      change Decidable (cell != 1)
      exact inferInstance
  | localizedDeficit =>
      exact .isTrue trivial

def localBudgetFor (_scenario : Scenario) (cell : Fin 3) : Int :=
  if cell = 0 then 1 else if cell = 1 then -2 else 0

/-- The exact finite order and negative-total theorem belong to the residual. -/
structure Residual where
  scenario : Scenario
  cells : Core.Finite.Enumeration (Fin 3)
  negativeTotal :
    (cells.values.map (localBudgetFor scenario)).sum < 0
  work_le_six : _root_.Hypostructure.CT11.localCheckBound cells <= 6

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def cellQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.cells

def scenarioAt (previous : Previous) : Scenario :=
  (Core.Residual.residualOf previous).scenario

abbrev spec : _root_.Hypostructure.CT11.Spec Previous where
  Cell := fun _previous => Fin 3
  Admissible := fun previous cell => admissibleFor (scenarioAt previous) cell
  localBudget := fun previous cell =>
    localBudgetFor (scenarioAt previous) cell

def negativeTotalQuery : Core.Residual.Query Previous fun previous =>
    ((cellQuery.read previous).values.map
      (spec.localBudget previous)).sum < 0 :=
  residualQuery.map fun previous _residual => by
    simpa [cellQuery, residualQuery, spec, scenarioAt] using
      (Core.Residual.residualOf previous).negativeTotal

def capability : _root_.Hypostructure.CT11.Capability spec where
  cells := cellQuery
  admissibleDecidable := fun previous cell =>
    admissibleForDecidable (scenarioAt previous) cell
  negativeTotal := negativeTotalQuery
  inputSize := fun _previous => 0
  workCoefficient := 6
  workDegree := 0
  workBound := fun previous => by
    change _root_.Hypostructure.CT11.localCheckBound
      (Core.Residual.residualOf previous).cells <= 6
    exact (Core.Residual.residualOf previous).work_le_six

def residual (scenario : Scenario) : Residual where
  scenario := scenario
  cells := threeCells
  negativeTotal := by
    cases scenario <;> decide
  work_le_six := by decide

def previous (scenario : Scenario) : Previous :=
  Core.Residual.Ledger.initial (residual scenario)

def gapResult :=
  _root_.Hypostructure.CT11.execute spec capability
    (previous .admissibilityGap)

def localizedResult :=
  _root_.Hypostructure.CT11.execute spec capability
    (previous .localizedDeficit)

theorem gap_terminal :
    gapResult.terminal = .admissibilityGap := by decide

theorem localized_terminal :
    localizedResult.terminal = .localizedDeficit := by decide

theorem gap_previous :
    gapResult.stage.previous = previous .admissibilityGap := rfl

theorem localized_previous :
    localizedResult.stage.previous = previous .localizedDeficit := rfl

/-- The first inadmissible cell is at schedule index one. -/
theorem gap_scan_checks :
    (_root_.Hypostructure.CT11.countedAdmissibilityScan capability
      (previous .admissibilityGap)).checks = 2 := by decide

/-- The localized branch exhausts all three admissibility checks. -/
theorem localized_admissibility_checks :
    (_root_.Hypostructure.CT11.countedAdmissibilityScan capability
      (previous .localizedDeficit)).checks = 3 := by decide

/-- Its first negative local budget is also at schedule index one. -/
theorem localized_budget_checks :
    (_root_.Hypostructure.CT11.countedNegativeScan capability
      (previous .localizedDeficit)).checks = 2 := by decide

theorem gap_checks : gapResult.checks = 2 := by decide

theorem localized_checks : localizedResult.checks = 5 := by decide

theorem gap_trace :
    gapResult.traceNodes =
      [.entry, .cellSchedule, .admissibilityScan,
        .admissibilityGapTerminal] := by decide

theorem localized_trace :
    localizedResult.traceNodes =
      [.entry, .cellSchedule, .admissibilityScan, .negativeTotal,
        .negativeBudgetScan, .localizedDeficitTerminal] := by decide

def gapResidual := gapResult.gapResidual gap_terminal

def localizedResidual :=
  localizedResult.localizedResidual localized_terminal

theorem gap_cell : gapResidual.value = 1 := by decide

theorem gap_cell_inadmissible :
    Not (spec.Admissible (previous .admissibilityGap) gapResidual.value) :=
  gapResidual.inadmissible

theorem localized_cell : localizedResidual.cell = 1 := by decide

theorem localized_cell_negative :
    spec.localBudget (previous .localizedDeficit) localizedResidual.cell < 0 :=
  localizedResidual.negative

theorem gap_verified :
    _root_.Hypostructure.CT11.OutcomeClaim gapResult.outcome :=
  gapResult.verified

theorem localized_verified :
    _root_.Hypostructure.CT11.OutcomeClaim localizedResult.outcome :=
  localizedResult.verified

theorem localized_work :
    localizedResult.checks <= capability.workCoefficient *
      (capability.inputSize (previous .localizedDeficit) + 1) ^
        capability.workDegree :=
  localizedResult.checks_le_polynomial

theorem gap_work :
    gapResult.checks <= capability.workCoefficient *
      (capability.inputSize (previous .admissibilityGap) + 1) ^
        capability.workDegree :=
  gapResult.checks_le_polynomial

def profile :
    _root_.Hypostructure.CT11.OrderedNegativeBudgetProfile Previous where
  Cell := fun _previous => Fin 3
  localBudget := spec.localBudget
  cells := cellQuery
  negativeTotal := negativeTotalQuery
  inputSize := fun _previous => 0
  workCoefficient := 6
  workDegree := 0
  workBound := capability.workBound

def profileResult := profile.run (previous .localizedDeficit)

theorem profile_terminal :
    profileResult.terminal = .localizedDeficit :=
  profile.run_terminal_localized (previous .localizedDeficit)

theorem profile_negative :
    profile.localBudget (previous .localizedDeficit)
      (profile.residual (previous .localizedDeficit)).cell < 0 :=
  profile.residual_negative (previous .localizedDeficit)

end Neutral

namespace GraphAdapter

open Hypostructure.Core
open Hypostructure.Graph

abbrev singletonGraph : FiniteObject where
  Vertex := Fin 1
  graph := ⊥
  vertices := inferInstance
  decideAdj := inferInstance

def objectQuery : Core.Residual.Query Neutral.Previous fun _previous =>
    FiniteObject :=
  Neutral.residualQuery.map fun _previous _residual => singletonGraph

abbrev spec := _root_.Hypostructure.Graph.CT11.additiveSpec objectQuery
  (fun _previous => Fin 3)
  (fun previous _object cell =>
    Neutral.admissibleFor (Neutral.scenarioAt previous) cell)
  (fun previous _object cell =>
    Neutral.localBudgetFor (Neutral.scenarioAt previous) cell)

def negativeTotalQuery :
    Core.Residual.Query Neutral.Previous fun previous =>
      ((Neutral.cellQuery.read previous).values.map
        (spec.localBudget previous)).sum < 0 :=
  Neutral.residualQuery.map fun previous _residual => by
    simpa [Neutral.cellQuery, Neutral.residualQuery, spec,
      Neutral.scenarioAt, objectQuery,
      _root_.Hypostructure.Graph.CT11.additiveSpec] using
      (Core.Residual.residualOf previous).negativeTotal

def capability : _root_.Hypostructure.CT11.Capability spec :=
  _root_.Hypostructure.Graph.CT11.additiveCapability objectQuery
    (fun _previous => Fin 3)
    (fun previous _object cell =>
      Neutral.admissibleFor (Neutral.scenarioAt previous) cell)
    (fun previous _object cell =>
      Neutral.localBudgetFor (Neutral.scenarioAt previous) cell)
    Neutral.cellQuery
    (fun previous cell =>
      Neutral.admissibleForDecidable (Neutral.scenarioAt previous) cell)
    negativeTotalQuery (fun _previous => 0) 6 0 (fun previous => by
      change _root_.Hypostructure.CT11.localCheckBound
        (Core.Residual.residualOf previous).cells <= 6
      exact (Core.Residual.residualOf previous).work_le_six)

def result := _root_.Hypostructure.CT11.execute spec capability
  (Neutral.previous .admissibilityGap)

theorem terminal : result.terminal = .admissibilityGap := by decide

theorem verified : _root_.Hypostructure.CT11.OutcomeClaim result.outcome :=
  result.verified

end GraphAdapter

namespace PDEAdapter

open Hypostructure.Core
open Hypostructure.PDE

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _state => True
  BranchState := fun _state => Unit

def atlas : LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _point _window => True
  nested := fun _left _right => True
  nested_refl := fun _window => trivial
  nested_trans := fun _leftToMiddle _middleToRight => trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Unit
  restrict := fun _state _window => ()
  restrictLocal := fun _nested _local => ()
  restrict_refl := fun _window _local => rfl
  restrict_trans := fun _leftToMiddle _middleToRight _local => rfl
  restrict_global := by
    intro _state _left _right _nested
    rfl

def equation : RepresentedEquation problem atlas where
  EquationData := fun _window _local => Unit
  satisfies := fun _data => True
  restrictEquation := fun _left _right data => data
  restrict_satisfies := fun _left _right _data valid => valid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def stateQuery : Core.Residual.Query Neutral.Previous fun _previous =>
    model.problem.Ambient :=
  Neutral.residualQuery.map fun _previous _residual => ()

abbrev spec := _root_.Hypostructure.PDE.CT11.additiveSpec model stateQuery
  (fun _previous => Fin 3)
  (fun previous _state cell =>
    Neutral.admissibleFor (Neutral.scenarioAt previous) cell)
  (fun previous _state cell =>
    Neutral.localBudgetFor (Neutral.scenarioAt previous) cell)

def negativeTotalQuery :
    Core.Residual.Query Neutral.Previous fun previous =>
      ((Neutral.cellQuery.read previous).values.map
        (spec.localBudget previous)).sum < 0 :=
  Neutral.residualQuery.map fun previous _residual => by
    simpa [Neutral.cellQuery, Neutral.residualQuery, spec,
      Neutral.scenarioAt, stateQuery,
      _root_.Hypostructure.PDE.CT11.additiveSpec] using
      (Core.Residual.residualOf previous).negativeTotal

def capability : _root_.Hypostructure.CT11.Capability spec :=
  _root_.Hypostructure.PDE.CT11.additiveCapability model stateQuery
    (fun _previous => Fin 3)
    (fun previous _state cell =>
      Neutral.admissibleFor (Neutral.scenarioAt previous) cell)
    (fun previous _state cell =>
      Neutral.localBudgetFor (Neutral.scenarioAt previous) cell)
    Neutral.cellQuery
    (fun previous cell =>
      Neutral.admissibleForDecidable (Neutral.scenarioAt previous) cell)
    negativeTotalQuery (fun _previous => 0) 6 0 (fun previous => by
      change _root_.Hypostructure.CT11.localCheckBound
        (Core.Residual.residualOf previous).cells <= 6
      exact (Core.Residual.residualOf previous).work_le_six)

def result := _root_.Hypostructure.CT11.execute spec capability
  (Neutral.previous .localizedDeficit)

theorem terminal : result.terminal = .localizedDeficit := by decide

theorem verified : _root_.Hypostructure.CT11.OutcomeClaim result.outcome :=
  result.verified

end PDEAdapter

#print axioms Neutral.gap_verified
#print axioms Neutral.localized_verified
#print axioms Neutral.profile_negative
#print axioms GraphAdapter.verified
#print axioms PDEAdapter.verified

end Hypostructure.Fixtures.CT11
