import Hypostructure.Graph.CT15
import Hypostructure.PDE.CT15

/-!
# CT15 vertical-slice fixtures

The three fixtures exercise the first-drop terminal and both full-rank
capacity outcomes.  Every coordinate schedule is stored in the root residual
and retrieved through a typed query.
-/

namespace Hypostructure.Fixtures.CT15

namespace FirstDrop

/-- The root residual owns the complete local rank-coordinate family. -/
structure Residual where
  coordinates : Core.Finite.Enumeration (Fin 3)

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def coordinatesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.coordinates

abbrev spec : _root_.Hypostructure.CT15.Spec Previous where
  Coordinate := fun _previous => Fin 3
  TargetDependent := fun _previous coordinate => coordinate = 1
  charge := fun _previous _coordinate => 4
  capacity := fun _previous => 20

def targetDependentDecidable (previous : Previous) (coordinate : Fin 3) :
    Decidable (spec.TargetDependent previous coordinate) := by
  change Decidable (coordinate = 1)
  infer_instance

def capability : _root_.Hypostructure.CT15.Capability spec where
  coordinates := coordinatesQuery
  targetDependentDecidable := targetDependentDecidable
  inputSize := fun previous => (coordinatesQuery.read previous).card
  workCoefficient := 2
  workDegree := 1
  workBound := by
    intro previous
    simp only [_root_.Hypostructure.CT15.localCheckBound, Nat.pow_one]
    omega

def residual : Residual where
  coordinates := Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT15.ExecutionResult spec capability :=
  _root_.Hypostructure.CT15.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem computed_rank :
    _root_.Hypostructure.CT15.computedRank capability previous = 2 := by
  decide

theorem terminal : result.terminal = .rankDrop := by decide

theorem exact_checks : result.checks = 5 := by decide

theorem exact_trace :
    result.traceNodes =
      [.entry, .rankComputation, .firstDropSearch, .rankDropTerminal] :=
  by decide

theorem first_drop_index :
    (_root_.Hypostructure.CT15.dropScan capability previous).index? = some 1 := by
  decide

theorem sound :
    _root_.Hypostructure.CT15.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end FirstDrop

namespace GraphCapacity

abbrev Vertex := Fin 2

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

structure Residual where
  object : Graph.FiniteObject
  coordinates : Core.Finite.Enumeration Bool

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  residualQuery.map fun _previous residual => residual.object

def coordinatesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.coordinates

abbrev Coordinate (_previous : Previous) := Bool

def TargetDependent (_previous : Previous) (_object : Graph.FiniteObject)
    (_coordinate : Bool) : Prop :=
  False

def charge (_previous : Previous) (_object : Graph.FiniteObject)
    (coordinate : Bool) : Nat :=
  if coordinate then 3 else 2

def capacity (_previous : Previous) (_object : Graph.FiniteObject) : Nat := 4

def spec := Graph.CT15.targetRelativeSpec objectQuery Coordinate
  TargetDependent charge capacity

def capability := Graph.CT15.targetRelativeCapability objectQuery Coordinate
  TargetDependent charge capacity coordinatesQuery
  (fun _previous _object _coordinate => .isFalse id)
  (fun previous => (coordinatesQuery.read previous).card) 2 1 (by
    intro previous
    simp only [_root_.Hypostructure.CT15.localCheckBound, Nat.pow_one]
    omega)

def residual : Residual where
  object := object
  coordinates :=
    Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT15.ExecutionResult spec capability :=
  _root_.Hypostructure.CT15.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem computed_full_rank :
    _root_.Hypostructure.CT15.computedRank capability previous = 2 := rfl

theorem exact_entries :
    _root_.Hypostructure.CT15.ledgerEntries capability previous =
      [(false, 2), (true, 3)] :=
  rfl

theorem exact_total :
    _root_.Hypostructure.CT15.ledgerTotal capability previous = 5 :=
  rfl

theorem terminal : result.terminal = .c4 := rfl

theorem exact_checks : result.checks = 5 := rfl

theorem exact_trace :
    result.traceNodes =
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .c4Terminal] :=
  rfl

theorem sound :
    _root_.Hypostructure.CT15.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end GraphCapacity

namespace PDECapacity

def problem : Core.Problem where
  Ambient := Unit
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
  LocalObject := fun _window => Unit
  restrict := fun _state _window => ()
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

def model : PDE.LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

structure Residual where
  state : Unit
  gaugeDirections : Core.Finite.Enumeration Bool

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def stateQuery : Core.Residual.Query Previous fun _previous =>
    model.problem.Ambient :=
  residualQuery.map fun _previous residual => residual.state

def coordinatesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.gaugeDirections

abbrev Coordinate (_previous : Previous) := Bool

def TargetDependent (_previous : Previous) (_state : model.problem.Ambient)
    (_direction : Bool) : Prop :=
  False

def charge (_previous : Previous) (_state : model.problem.Ambient)
    (direction : Bool) : Nat :=
  if direction then 2 else 1

def capacity (_previous : Previous) (_state : model.problem.Ambient) : Nat := 3

def spec := PDE.CT15.targetRelativeSpec model stateQuery Coordinate
  TargetDependent charge capacity

def capability := PDE.CT15.targetRelativeCapability model stateQuery Coordinate
  TargetDependent charge capacity coordinatesQuery
  (fun _previous _state _coordinate => .isFalse id)
  (fun previous => (coordinatesQuery.read previous).card) 2 1 (by
    intro previous
    simp only [_root_.Hypostructure.CT15.localCheckBound, Nat.pow_one]
    omega)

def residual : Residual where
  state := ()
  gaugeDirections :=
    Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT15.ExecutionResult spec capability :=
  _root_.Hypostructure.CT15.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem computed_full_rank :
    _root_.Hypostructure.CT15.computedRank capability previous = 2 := rfl

theorem exact_entries :
    _root_.Hypostructure.CT15.ledgerEntries capability previous =
      [(false, 1), (true, 2)] :=
  rfl

theorem exact_total :
    _root_.Hypostructure.CT15.ledgerTotal capability previous = 3 :=
  rfl

theorem terminal : result.terminal = .fullRankLedger := rfl

theorem exact_checks : result.checks = 5 := rfl

theorem exact_trace :
    result.traceNodes =
      [.entry, .rankComputation, .firstDropSearch, .ledgerComputation,
        .capacityComparison, .fullRankLedgerTerminal] :=
  rfl

theorem sound :
    _root_.Hypostructure.CT15.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end PDECapacity

#print axioms FirstDrop.retains_predecessor
#print axioms FirstDrop.computed_rank
#print axioms FirstDrop.first_drop_index
#print axioms FirstDrop.exact_checks
#print axioms FirstDrop.exact_trace
#print axioms FirstDrop.sound
#print axioms FirstDrop.polynomial_work
#print axioms GraphCapacity.computed_full_rank
#print axioms GraphCapacity.exact_entries
#print axioms GraphCapacity.terminal
#print axioms GraphCapacity.exact_checks
#print axioms GraphCapacity.exact_trace
#print axioms GraphCapacity.sound
#print axioms PDECapacity.computed_full_rank
#print axioms PDECapacity.exact_entries
#print axioms PDECapacity.terminal
#print axioms PDECapacity.exact_checks
#print axioms PDECapacity.exact_trace
#print axioms PDECapacity.sound

end Hypostructure.Fixtures.CT15
