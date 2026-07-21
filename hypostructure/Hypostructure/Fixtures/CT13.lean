import Hypostructure.Graph.CT13
import Hypostructure.PDE.CT13
import Hypostructure.Fixtures.GraphBasics
import Hypostructure.Fixtures.PDEBasics

/-!
# CT13 vertical-slice fixtures

The neutral fixture reaches all four terminals from one residual shape and
pins primary order, first-minimum fallback tie-breaking, pairwise overlap
order, exact traces, and exact work.  Graph and PDE fixtures instantiate the
same machine through thin state-reading adapters.
-/

namespace Hypostructure.Fixtures.CT13

namespace Neutral

open Hypostructure.Core

inductive Scenario where
  | tierOne
  | overlap
  | deficit
  | reconciled
  deriving DecidableEq, Repr

def payerOrder : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def obstructionOrder : _root_.Hypostructure.CT13.ObstructionSchedule (Fin 2) where
  fallbackDefault := 0
  remaining := [1]
  nodup := by decide
  decEq := inferInstance

def tierTwoOrder (_obstruction : Fin 2) :
    Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1] (by decide)

/-- Literal predecessor residual containing every finite schedule inspected
by CT13 and its local work certificate. -/
structure Residual where
  scenario : Scenario
  payers : Core.Finite.Enumeration (Fin 3)
  obstructions : _root_.Hypostructure.CT13.ObstructionSchedule (Fin 2)
  tierTwo : Fin 2 -> Core.Finite.Enumeration (Fin 3)
  work_le_twentyFive :
    _root_.Hypostructure.CT13.localCheckBound payers obstructions tierTwo <= 25

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def payerQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.payers

def obstructionQuery : Core.Residual.Query Previous fun _previous =>
    _root_.Hypostructure.CT13.ObstructionSchedule (Fin 2) :=
  residualQuery.map fun _previous residual => residual.obstructions

def tierTwoQuery : Core.Residual.Query Previous fun _previous =>
    Fin 2 -> Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.tierTwo

def scenarioAt (previous : Previous) : Scenario :=
  (Core.Residual.residualOf previous).scenario

def eligible (previous : Previous) (payer : Fin 3) : Prop :=
  scenarioAt previous = .tierOne ∧ payer = 1

/-- Nonterminal scenarios select obstruction one; the reconciled scenario has
an exact tie and therefore retains the default obstruction zero. -/
def obstructionCost (previous : Previous) (obstruction : Fin 2) : Nat :=
  if scenarioAt previous = .reconciled then 0
  else if obstruction = 1 then 0 else 1

def payerResource (previous : Previous) (payer : Fin 3) : Bool :=
  if scenarioAt previous = .overlap then false else payer == 1

def charge (_previous : Previous) (_payer : Fin 3) : Nat := 1

def demand (previous : Previous) : Nat :=
  if scenarioAt previous = .deficit then 3 else 2

abbrev spec : _root_.Hypostructure.CT13.Spec Previous where
  Payer := fun _previous => Fin 3
  Obstruction := fun _previous => Fin 2
  Resource := fun _previous => Bool
  Eligible := eligible
  obstructionCost := obstructionCost
  payerResource := payerResource
  charge := charge
  demand := demand

def capability : _root_.Hypostructure.CT13.Capability spec where
  payers := payerQuery
  obstructions := obstructionQuery
  tierTwo := tierTwoQuery
  eligibleDecidable := fun previous payer => by
    change Decidable (scenarioAt previous = .tierOne ∧ payer = 1)
    infer_instance
  resourceDecidableEq := fun _previous => inferInstance
  inputSize := fun _previous => 0
  workCoefficient := 25
  workDegree := 0
  workBound := fun previous => by
    change _root_.Hypostructure.CT13.localCheckBound
      (Core.Residual.residualOf previous).payers
      (Core.Residual.residualOf previous).obstructions
      (Core.Residual.residualOf previous).tierTwo <= 25
    exact (Core.Residual.residualOf previous).work_le_twentyFive

def residual (scenario : Scenario) : Residual where
  scenario := scenario
  payers := payerOrder
  obstructions := obstructionOrder
  tierTwo := tierTwoOrder
  work_le_twentyFive := by decide

def previous (scenario : Scenario) : Previous :=
  Core.Residual.Ledger.initial (residual scenario)

def tierOneResult :=
  _root_.Hypostructure.CT13.execute spec capability (previous .tierOne)

def overlapResult :=
  _root_.Hypostructure.CT13.execute spec capability (previous .overlap)

def deficitResult :=
  _root_.Hypostructure.CT13.execute spec capability (previous .deficit)

def reconciledResult :=
  _root_.Hypostructure.CT13.execute spec capability (previous .reconciled)

theorem tierOne_terminal : tierOneResult.terminal = .tierOne := by decide
theorem overlap_terminal : overlapResult.terminal = .overlap := by decide
theorem deficit_terminal : deficitResult.terminal = .deficit := by decide
theorem reconciled_terminal : reconciledResult.terminal = .reconciled := by decide

theorem tierOne_previous :
    tierOneResult.stage.previous = previous .tierOne := rfl

theorem reconciled_previous :
    reconciledResult.stage.previous = previous .reconciled := rfl

theorem tierOne_checks : tierOneResult.checks = 2 := by decide
theorem overlap_checks : overlapResult.checks = 6 := by decide
theorem deficit_checks : deficitResult.checks = 11 := by decide
theorem reconciled_checks : reconciledResult.checks = 11 := by decide

theorem tierOne_trace : tierOneResult.traceNodes =
    [.entry, .payerSchedule, .tierOneSearch, .tierOneTerminal] := by decide

theorem overlap_trace : overlapResult.traceNodes =
    [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
      .fallbackSelection, .tierTwoSchedule, .overlapSearch,
      .overlapTerminal] := by decide

theorem deficit_trace : deficitResult.traceNodes =
    [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
      .fallbackSelection, .tierTwoSchedule, .overlapSearch,
      .reconciliationLedger, .comparison, .deficitTerminal] := by decide

theorem reconciled_trace : reconciledResult.traceNodes =
    [.entry, .payerSchedule, .tierOneSearch, .obstructionSchedule,
      .fallbackSelection, .tierTwoSchedule, .overlapSearch,
      .reconciliationLedger, .comparison, .reconciledTerminal] := by decide

/-- Strictly lower cost selects obstruction one. -/
theorem deficit_fallback_selected :
    deficitResult.selectedFallback? = some 1 := by decide

/-- Equal costs retain the first/default obstruction, pinning canonical
tie-breaking. -/
theorem reconciled_tie_retains_default :
    reconciledResult.selectedFallback? = some 0 := by decide

/-- Product order first inspects `(0,0)`, then selects overlap `(0,1)`. -/
theorem overlap_first_pair :
    overlapResult.overlapIndex? = some 1 ∧
      overlapResult.overlapPair? = some (0, 1) := by decide

theorem tierOne_verified :
    _root_.Hypostructure.CT13.OutcomeClaim tierOneResult.outcome :=
  tierOneResult.verified

theorem overlap_verified :
    _root_.Hypostructure.CT13.OutcomeClaim overlapResult.outcome :=
  overlapResult.verified

theorem deficit_verified :
    _root_.Hypostructure.CT13.OutcomeClaim deficitResult.outcome :=
  deficitResult.verified

theorem reconciled_verified :
    _root_.Hypostructure.CT13.OutcomeClaim reconciledResult.outcome :=
  reconciledResult.verified

theorem reconciled_total : Exists fun result :
    _root_.Hypostructure.CT13.ExecutionResult spec capability =>
    result.stage.previous = previous .reconciled ∧
    _root_.Hypostructure.CT13.OutcomeClaim result.outcome ∧
    result.traceNodes =
      _root_.Hypostructure.CT13.Trace.expectedNodes result.terminal ∧
    result.checks <= capability.workCoefficient *
      (capability.inputSize (previous .reconciled) + 1) ^
        capability.workDegree := by
  ct13_total (previous .reconciled) using capability

end Neutral

namespace GraphAdapter

open Hypostructure.Core
open Hypostructure.Graph

def objectQuery : Core.Residual.Query Neutral.Previous fun _previous =>
    FiniteObject :=
  Neutral.residualQuery.map fun _previous _residual =>
    Hypostructure.Fixtures.GraphBasics.k4

abbrev spec := _root_.Hypostructure.Graph.CT13.tieredSpec objectQuery
  (fun _previous => Fin 3) (fun _previous => Fin 2)
  (fun _previous => Bool)
  (fun _previous object payer => object.edgeCount = 0 ∧ payer = 1)
  (fun previous _object obstruction =>
    Neutral.obstructionCost previous obstruction)
  (fun previous _object payer => Neutral.payerResource previous payer)
  (fun _previous object _payer => if 0 < object.vertexCount then 1 else 0)
  (fun _previous object => if 0 < object.vertexCount then 2 else 0)

def capability : _root_.Hypostructure.CT13.Capability spec :=
  _root_.Hypostructure.Graph.CT13.tieredCapability objectQuery
    (fun _previous => Fin 3) (fun _previous => Fin 2)
    (fun _previous => Bool)
    (fun _previous object payer => object.edgeCount = 0 ∧ payer = 1)
    (fun previous _object obstruction =>
      Neutral.obstructionCost previous obstruction)
    (fun previous _object payer => Neutral.payerResource previous payer)
    (fun _previous object _payer => if 0 < object.vertexCount then 1 else 0)
    (fun _previous object => if 0 < object.vertexCount then 2 else 0)
    Neutral.payerQuery Neutral.obstructionQuery Neutral.tierTwoQuery
    (fun _previous object payer =>
      inferInstanceAs (Decidable (object.edgeCount = 0 ∧ payer = 1)))
    (fun _previous => inferInstance) (fun _previous => 0) 25 0
    (fun previous => by
      change _root_.Hypostructure.CT13.localCheckBound
        (Core.Residual.residualOf previous).payers
        (Core.Residual.residualOf previous).obstructions
        (Core.Residual.residualOf previous).tierTwo <= 25
      exact (Core.Residual.residualOf previous).work_le_twentyFive)

def result := _root_.Hypostructure.CT13.execute spec capability
  (Neutral.previous .reconciled)

theorem terminal : result.terminal = .reconciled := by decide

theorem verified : _root_.Hypostructure.CT13.OutcomeClaim result.outcome :=
  result.verified

theorem retained_object :
    objectQuery.read result.stage.previous =
      Hypostructure.Fixtures.GraphBasics.k4 := rfl

end GraphAdapter

namespace PDEAdapter

open Hypostructure.Core
open Hypostructure.PDE

abbrev Model := Hypostructure.Fixtures.PDEBasics.FiniteRestriction.model
abbrev Field := Model.problem.Ambient

def stateQuery : Core.Residual.Query Neutral.Previous fun _previous => Field :=
  Neutral.residualQuery.map fun _previous _residual =>
    Hypostructure.Fixtures.PDEBasics.FiniteRestriction.sample

abbrev spec := _root_.Hypostructure.PDE.CT13.tieredSpec Model stateQuery
  (fun _previous => Fin 3) (fun _previous => Fin 2)
  (fun _previous => Bool)
  (fun _previous state payer => state 0 < 0 ∧ payer = 1)
  (fun previous _state obstruction =>
    Neutral.obstructionCost previous obstruction)
  (fun previous _state payer => Neutral.payerResource previous payer)
  (fun _previous state _payer => if state 0 = 0 then 1 else 0)
  (fun _previous state => if state 0 = 0 then 2 else 0)

def capability : _root_.Hypostructure.CT13.Capability spec :=
  _root_.Hypostructure.PDE.CT13.tieredCapability Model stateQuery
    (fun _previous => Fin 3) (fun _previous => Fin 2)
    (fun _previous => Bool)
    (fun _previous state payer => state 0 < 0 ∧ payer = 1)
    (fun previous _state obstruction =>
      Neutral.obstructionCost previous obstruction)
    (fun previous _state payer => Neutral.payerResource previous payer)
    (fun _previous state _payer => if state 0 = 0 then 1 else 0)
    (fun _previous state => if state 0 = 0 then 2 else 0)
    Neutral.payerQuery Neutral.obstructionQuery Neutral.tierTwoQuery
    (fun _previous state payer =>
      inferInstanceAs (Decidable (state 0 < 0 ∧ payer = 1)))
    (fun _previous => inferInstance) (fun _previous => 0) 25 0
    (fun previous => by
      change _root_.Hypostructure.CT13.localCheckBound
        (Core.Residual.residualOf previous).payers
        (Core.Residual.residualOf previous).obstructions
        (Core.Residual.residualOf previous).tierTwo <= 25
      exact (Core.Residual.residualOf previous).work_le_twentyFive)

def result := _root_.Hypostructure.CT13.execute spec capability
  (Neutral.previous .reconciled)

theorem terminal : result.terminal = .reconciled := by decide

theorem verified : _root_.Hypostructure.CT13.OutcomeClaim result.outcome :=
  result.verified

theorem retained_state :
    stateQuery.read result.stage.previous =
      Hypostructure.Fixtures.PDEBasics.FiniteRestriction.sample := rfl

end PDEAdapter

#print axioms Neutral.tierOne_verified
#print axioms Neutral.overlap_verified
#print axioms Neutral.deficit_verified
#print axioms Neutral.reconciled_verified
#print axioms Neutral.reconciled_total
#print axioms GraphAdapter.verified
#print axioms PDEAdapter.verified
#print axioms _root_.Hypostructure.CT13.outcomeChecks_le_limit
#print axioms _root_.Hypostructure.CT13.run_total

end Hypostructure.Fixtures.CT13
