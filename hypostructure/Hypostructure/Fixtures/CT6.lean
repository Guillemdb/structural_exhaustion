import Hypostructure.Graph.CT6
import Hypostructure.PDE.CT6

/-!
# CT6 vertical-slice fixtures

The graph fixture reaches the canonical first-failure terminal.  The PDE
fixture exhausts its exact predecessor-owned order and checks the generated
active ledger, total, trace, and work count.
-/

namespace Hypostructure.Fixtures.CT6

namespace GraphFirstFailure

abbrev Vertex := Fin 2

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

/-- The root residual owns both the graph and its ordered monitored slots. -/
structure Residual where
  object : Graph.FiniteObject
  sites : Core.Finite.Enumeration (Fin 3)

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  residualQuery.map fun _previous residual => residual.object

def siteQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.sites

abbrev Site (_previous : Previous) := Fin 3

abbrev FailureData (_previous : Previous) (_site : Fin 3) := Nat

/-- A monitored vertex slot fails exactly when the graph has no vertex there. -/
def failure (_previous : Previous) (object : Graph.FiniteObject)
    (site : Fin 3) : Prop :=
  object.vertices.card ≤ site.1

def failureData (_previous : Previous) (_object : Graph.FiniteObject)
    (site : Fin 3) (_failed : failure _previous _object site) : Nat :=
  site.1

def contribution (_previous : Previous) (_object : Graph.FiniteObject)
    (_site : Fin 3) : Nat :=
  1

abbrev spec := Graph.CT6.orderedActivitySpec objectQuery Site FailureData
  failure failureData contribution

def capability := Graph.CT6.orderedActivityCapability objectQuery Site
  FailureData failure failureData contribution siteQuery
  (fun _previous object site => Nat.decLe object.vertices.card site.1)
  (fun previous => (siteQuery.read previous).card) 1 1 (by
    intro previous
    simp only [_root_.Hypostructure.CT6.localCheckBound, one_mul, Nat.pow_one]
    omega)

def residual : Residual where
  object := object
  sites := Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT6.ExecutionResult spec capability :=
  _root_.Hypostructure.CT6.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem first_index :
    (_root_.Hypostructure.CT6.activityScan capability previous).index? =
      some 2 := by
  decide

theorem terminal : result.terminal = .firstFailure := by
  decide

theorem exact_checks : result.checks = 3 := by
  decide

theorem exact_trace :
    result.traceNodes =
      [.entry, .failureOrder, .activityScan, .firstFailureTerminal] := by
  decide

theorem sound : _root_.Hypostructure.CT6.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks ≤ capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end GraphFirstFailure

namespace PDEActiveLedger

abbrev problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _state => True
  BranchState := fun _state => Unit

def atlas : PDE.LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _point _window => True
  nested := fun _small _large => True
  nested_refl := fun _window => trivial
  nested_trans := fun _first _second => trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Nat
  restrict := fun state _window => state
  restrictLocal := fun _nested object => object
  restrict_refl := fun _window _object => rfl
  restrict_trans := fun _smallLarge _largeWork _object => rfl
  restrict_global := by
    intro state small large nested
    rfl

def equation : PDE.RepresentedEquation problem atlas where
  EquationData := fun _window _object => Unit
  satisfies := fun _data => True
  restrictEquation := fun _nested _object data => data
  restrict_satisfies := fun _nested _object _data valid => valid

abbrev model : PDE.LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

/-- The PDE residual owns its represented state and ordered row family. -/
structure Residual where
  state : Nat
  rows : Core.Finite.Enumeration (Fin 3)

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def stateQuery : Core.Residual.Query Previous fun _previous =>
    model.problem.Ambient :=
  residualQuery.map fun _previous residual => residual.state

def rowQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.rows

abbrev Row (_previous : Previous) := Fin 3

abbrev FailureData (_previous : Previous) (_row : Fin 3) := Nat

/-- A toy ordered PDE row fails when its threshold reaches the state level. -/
def failure (_previous : Previous) (state : model.problem.Ambient)
    (row : Fin 3) : Prop :=
  state ≤ row.1

def failureData (_previous : Previous) (state : model.problem.Ambient)
    (row : Fin 3) (_failed : failure _previous state row) : Nat :=
  state + row.1

def contribution (_previous : Previous) (state : model.problem.Ambient)
    (row : Fin 3) : Nat :=
  state - row.1

abbrev spec := PDE.CT6.orderedActivitySpec model stateQuery Row FailureData
  failure failureData contribution

def capability := PDE.CT6.orderedActivityCapability model stateQuery Row
  FailureData failure failureData contribution rowQuery
  (fun _previous state row => Nat.decLe state row.1)
  (fun previous => (rowQuery.read previous).card) 1 1 (by
    intro previous
    simp only [_root_.Hypostructure.CT6.localCheckBound, one_mul, Nat.pow_one]
    omega)

def residual : Residual where
  state := 3
  rows := Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT6.ExecutionResult spec capability :=
  _root_.Hypostructure.CT6.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem no_failure :
    (_root_.Hypostructure.CT6.activityScan capability previous).index? =
      none := by
  decide

theorem terminal : result.terminal = .activeLedger := by
  decide

theorem exact_entries :
    _root_.Hypostructure.CT6.activeEntries capability previous =
      [((0 : Fin 3), 3), ((1 : Fin 3), 2), ((2 : Fin 3), 1)] :=
  rfl

theorem exact_total :
    _root_.Hypostructure.CT6.activeTotal capability previous = 6 :=
  rfl

theorem exact_checks : result.checks = 3 := by
  decide

theorem exact_trace :
    result.traceNodes =
      [.entry, .failureOrder, .activityScan, .activeLedgerComputation,
        .activeLedgerTerminal] := by
  decide

theorem sound : _root_.Hypostructure.CT6.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks ≤ capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end PDEActiveLedger

#print axioms GraphFirstFailure.retains_predecessor
#print axioms GraphFirstFailure.first_index
#print axioms GraphFirstFailure.terminal
#print axioms GraphFirstFailure.exact_checks
#print axioms GraphFirstFailure.exact_trace
#print axioms GraphFirstFailure.sound
#print axioms GraphFirstFailure.polynomial_work
#print axioms PDEActiveLedger.no_failure
#print axioms PDEActiveLedger.terminal
#print axioms PDEActiveLedger.exact_entries
#print axioms PDEActiveLedger.exact_total
#print axioms PDEActiveLedger.exact_checks
#print axioms PDEActiveLedger.exact_trace
#print axioms PDEActiveLedger.sound
#print axioms PDEActiveLedger.polynomial_work

end Hypostructure.Fixtures.CT6
