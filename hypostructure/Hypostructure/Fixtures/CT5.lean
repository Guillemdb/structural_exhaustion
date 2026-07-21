import Hypostructure.Graph.CT5
import Hypostructure.PDE.CT5
import Hypostructure.Fixtures.Budgets
import Hypostructure.Fixtures.GraphBasics
import Hypostructure.Fixtures.PDEBasics

/-!
# CT5 vertical-slice fixtures

The neutral fixture reaches every terminal with residual-owned dependent
schedules.  Additional Graph and PDE fixtures show that both adapters execute
the identical Core machine without introducing domain routes or outcomes.
-/

namespace Hypostructure.Fixtures.CT5

open Hypostructure.Core

namespace Neutral

def boolSites : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

def oneSite : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.singleton false

def oneWitness : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.singleton false

def family (sites : Core.Finite.Enumeration Bool) :
    Core.Finite.DependentEnumeration Bool (fun _site => Bool) where
  indices := sites
  fibres := fun _site => oneWitness

/-- Literal incoming residual containing the exact local family and all
primitive semantics used by the fixture. -/
structure Residual where
  localFamily : Core.Finite.DependentEnumeration Bool (fun _site => Bool)
  active : Bool -> Bool
  supports : Bool -> Bool -> Bool
  amount : Bool -> Bool -> Nat
  required : Nat
  capacity : Nat

abbrev Previous := Core.Residual.Ledger Residual

abbrev spec : _root_.Hypostructure.CT5.Spec Previous where
  budget := Hypostructure.Fixtures.Budgets.naturalResource
  Site := fun _previous => Bool
  Witness := fun _previous _site => Bool
  Active := fun previous site =>
    (Core.Residual.residualOf previous).active site = true
  Supports := fun previous site witness =>
    (Core.Residual.residualOf previous).supports site witness = true
  contribution := fun previous site witness =>
    (Core.Residual.residualOf previous).amount site witness
  required := fun previous => (Core.Residual.residualOf previous).required
  capacity := fun previous => (Core.Residual.residualOf previous).capacity

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def familyQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.DependentEnumeration Bool (fun _site => Bool) :=
  residualQuery.map fun _previous residual => residual.localFamily

def capability : _root_.Hypostructure.CT5.Capability spec where
  family := familyQuery
  activeDecidable := fun previous site =>
    Bool.decEq ((Core.Residual.residualOf previous).active site) true
  supportsDecidable := fun previous site witness =>
    Bool.decEq
      ((Core.Residual.residualOf previous).supports site witness) true
  resourceLEDecidable := Nat.decLe

def deficitResidual : Residual where
  localFamily := family boolSites
  active := fun _site => true
  supports := fun site _witness => !site
  amount := fun _site _witness => 1
  required := 1
  capacity := 2

def c4Residual : Residual where
  localFamily := family oneSite
  active := fun _site => true
  supports := fun _site _witness => true
  amount := fun _site _witness => 2
  required := 3
  capacity := 1

def chargeResidual : Residual where
  localFamily := family oneSite
  active := fun _site => true
  supports := fun _site _witness => true
  amount := fun _site _witness => 1
  required := 1
  capacity := 2

def aggregateResidual : Residual where
  localFamily := family oneSite
  active := fun _site => true
  supports := fun _site _witness => true
  amount := fun _site _witness => 3
  required := 1
  capacity := 2

def deficitPrevious : Previous := Core.Residual.Ledger.initial deficitResidual
def c4Previous : Previous := Core.Residual.Ledger.initial c4Residual
def chargePrevious : Previous := Core.Residual.Ledger.initial chargeResidual
def aggregatePrevious : Previous :=
  Core.Residual.Ledger.initial aggregateResidual

def deficitResult :=
  _root_.Hypostructure.CT5.execute spec capability deficitPrevious
def c4Result := _root_.Hypostructure.CT5.execute spec capability c4Previous
def chargeResult :=
  _root_.Hypostructure.CT5.execute spec capability chargePrevious
def aggregateResult :=
  _root_.Hypostructure.CT5.execute spec capability aggregatePrevious

theorem deficit_previous : deficitResult.stage.previous = deficitPrevious := rfl
theorem deficit_terminal : deficitResult.terminal = .deficit := by decide
theorem c4_terminal : c4Result.terminal = .c4 := by decide
theorem charge_terminal : chargeResult.terminal = .chargeLedger := by decide
theorem aggregate_terminal : aggregateResult.terminal = .aggregate := by decide

theorem deficit_checks : deficitResult.checks = 4 := by decide
theorem c4_checks : c4Result.checks = 4 := by decide
theorem charge_checks : chargeResult.checks = 5 := by decide
theorem aggregate_checks : aggregateResult.checks = 5 := by decide

theorem deficit_trace : deficitResult.traceNodes =
    [.entry, .deficitSearch, .deficitTerminal] := by decide
theorem c4_trace : c4Result.traceNodes =
    [.entry, .deficitSearch, .ledgerComputation, .comparison, .c4Terminal] :=
  by decide
theorem charge_trace : chargeResult.traceNodes =
    [.entry, .deficitSearch, .ledgerComputation, .comparison,
      .chargeLedgerTerminal] := by decide
theorem aggregate_trace : aggregateResult.traceNodes =
    [.entry, .deficitSearch, .ledgerComputation, .comparison,
      .aggregateTerminal] := by decide

theorem deficit_verified :
    _root_.Hypostructure.CT5.OutcomeClaim spec capability deficitPrevious
      deficitResult.terminal :=
  deficitResult.verified

theorem c4_verified :
    _root_.Hypostructure.CT5.OutcomeClaim spec capability c4Previous
      c4Result.terminal :=
  c4Result.verified

theorem charge_verified :
    _root_.Hypostructure.CT5.OutcomeClaim spec capability chargePrevious
      chargeResult.terminal :=
  chargeResult.verified

theorem aggregate_verified :
    _root_.Hypostructure.CT5.OutcomeClaim spec capability aggregatePrevious
      aggregateResult.terminal :=
  aggregateResult.verified

theorem aggregate_total : Exists fun result :
    _root_.Hypostructure.CT5.ExecutionResult spec capability =>
    result.stage.previous = aggregatePrevious /\
    _root_.Hypostructure.CT5.OutcomeClaim spec capability aggregatePrevious
      result.terminal /\
    result.traceNodes =
      _root_.Hypostructure.CT5.Trace.expectedNodes result.terminal /\
    result.checks <= (capability.linearWorkBudget).coefficient *
      ((capability.linearWorkBudget).size aggregatePrevious + 1) ^
        (capability.linearWorkBudget).degree := by
  ct5_total aggregatePrevious using capability

end Neutral

namespace Graph

open Hypostructure.Graph

structure Residual where
  object : FiniteObject
  localFamily : Core.Finite.DependentEnumeration Unit (fun _site => Unit)

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous => FiniteObject :=
  residualQuery.map fun _previous residual => residual.object

def familyQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.DependentEnumeration Unit (fun _site => Unit) :=
  residualQuery.map fun _previous residual => residual.localFamily

abbrev spec := _root_.Hypostructure.Graph.CT5.localWitnessSpec objectQuery
  Hypostructure.Fixtures.Budgets.naturalResource
  (fun _previous => Unit) (fun _previous _site => Unit)
  (fun _previous object _site => 0 < object.vertexCount)
  (fun _previous object _site _witness => 0 < object.edgeCount)
  (fun _previous object _site _witness => object.edgeCount)
  (fun _previous _object => (1 : Nat))
  (fun _previous _object => (10 : Nat))

def capability : _root_.Hypostructure.CT5.Capability spec :=
  _root_.Hypostructure.Graph.CT5.localWitnessCapability objectQuery
    Hypostructure.Fixtures.Budgets.naturalResource
    (fun _previous => Unit) (fun _previous _site => Unit)
    (fun _previous object _site => 0 < object.vertexCount)
    (fun _previous object _site _witness => 0 < object.edgeCount)
    (fun _previous object _site _witness => object.edgeCount)
    (fun _previous _object => (1 : Nat))
    (fun _previous _object => (10 : Nat))
    familyQuery
    (fun _previous object _site => Nat.decLt 0 object.vertexCount)
    (fun _previous object _site _witness => Nat.decLt 0 object.edgeCount)
    Nat.decLe

def residual : Residual where
  object := Hypostructure.Fixtures.GraphBasics.k4
  localFamily := {
    indices := Core.Finite.Enumeration.singleton ()
    fibres := fun _site => Core.Finite.Enumeration.singleton ()
  }

def previous : Previous := Core.Residual.Ledger.initial residual
def result := _root_.Hypostructure.CT5.execute spec capability previous

theorem terminal : result.terminal = .chargeLedger := by decide
theorem retained_object :
    (Core.Residual.residualOf result.stage).object = residual.object := rfl

end Graph

namespace PDE

open Hypostructure.PDE

abbrev Model := Hypostructure.Fixtures.PDEBasics.FiniteRestriction.model
abbrev Field := Model.problem.Ambient

structure Residual where
  state : Field
  localFamily : Core.Finite.DependentEnumeration Unit (fun _site => Unit)

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def stateQuery : Core.Residual.Query Previous fun _previous => Field :=
  residualQuery.map fun _previous residual => residual.state

def familyQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.DependentEnumeration Unit (fun _site => Unit) :=
  residualQuery.map fun _previous residual => residual.localFamily

abbrev spec := _root_.Hypostructure.PDE.CT5.localWitnessSpec Model stateQuery
  Hypostructure.Fixtures.Budgets.naturalResource
  (fun _previous => Unit) (fun _previous _site => Unit)
  (fun _previous _state _site => True)
  (fun _previous _state _site _witness => True)
  (fun _previous _state _site _witness => (3 : Nat))
  (fun _previous _state => (1 : Nat))
  (fun _previous _state => (2 : Nat))

def capability : _root_.Hypostructure.CT5.Capability spec :=
  _root_.Hypostructure.PDE.CT5.localWitnessCapability Model stateQuery
    Hypostructure.Fixtures.Budgets.naturalResource
    (fun _previous => Unit) (fun _previous _site => Unit)
    (fun _previous _state _site => True)
    (fun _previous _state _site _witness => True)
    (fun _previous _state _site _witness => (3 : Nat))
    (fun _previous _state => (1 : Nat))
    (fun _previous _state => (2 : Nat))
    familyQuery
    (fun _previous _state _site => inferInstance)
    (fun _previous _state _site _witness => inferInstance)
    Nat.decLe

def residual : Residual where
  state := Hypostructure.Fixtures.PDEBasics.FiniteRestriction.sample
  localFamily := {
    indices := Core.Finite.Enumeration.singleton ()
    fibres := fun _site => Core.Finite.Enumeration.singleton ()
  }

def previous : Previous := Core.Residual.Ledger.initial residual
def result := _root_.Hypostructure.CT5.execute spec capability previous

theorem terminal : result.terminal = .aggregate := by decide
theorem retained_state :
    (Core.Residual.residualOf result.stage).state = residual.state := rfl

end PDE

#print axioms Neutral.deficit_verified
#print axioms Neutral.c4_verified
#print axioms Neutral.charge_verified
#print axioms Neutral.aggregate_verified
#print axioms Graph.terminal
#print axioms PDE.terminal
#print axioms _root_.Hypostructure.CT5.supportOfDeficitFree
#print axioms _root_.Hypostructure.CT5.DeficitFreeState.contribution_supported
#print axioms _root_.Hypostructure.CT5.outcomeChecks_le_limit
#print axioms _root_.Hypostructure.CT5.run_total

end Hypostructure.Fixtures.CT5
