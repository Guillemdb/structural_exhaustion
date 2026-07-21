import Hypostructure.Graph.CT9
import Hypostructure.PDE.CT9

/-!
# CT9 vertical-slice fixtures

The neutral fixture exercises both terminals on one residual-owned item
schedule and pins first-hit order, exact work, capacity forcing, and
capacity-one extraction.  A parity profile and thin Graph/PDE adapters execute
the same shared machine.
-/

namespace Hypostructure.Fixtures.CT9

namespace Neutral

inductive Scenario where
  | overloaded
  | bounded
  deriving DecidableEq, Repr

/-- Exact incoming item schedule. -/
def threeItems : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

/-- Pinned search order for the two authored labels. -/
def boolSchedule : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

/-- Complete authored label universe with that pinned search order. -/
def boolLabels : Core.Finite.CompleteEnumeration Bool where
  toEnumeration := boolSchedule
  complete := by
    intro label
    cases label <;> decide

/-- The literal predecessor owns the active items and their exact identity. -/
structure Residual where
  scenario : Scenario
  items : Core.Finite.Enumeration (Fin 3)
  items_eq : items = threeItems

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def itemQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.items

def scenarioAt (previous : Previous) : Scenario :=
  (Core.Residual.residualOf previous).scenario

def itemLabel (previous : Previous) (item : Fin 3) : Bool :=
  match scenarioAt previous with
  | .overloaded => false
  | .bounded => if item = 2 then true else false

def labelCapacity (previous : Previous) (_label : Bool) : Nat :=
  match scenarioAt previous with
  | .overloaded => 1
  | .bounded => 2

abbrev spec : _root_.Hypostructure.CT9.Spec Previous where
  Item := fun _previous => Fin 3
  Label := fun _previous => Bool
  label := itemLabel
  capacity := labelCapacity

def capability : _root_.Hypostructure.CT9.Capability spec where
  items := itemQuery
  labels := fun _previous => boolLabels
  inputSize := fun _previous => 0
  workCoefficient := 8
  workDegree := 0
  workBound := by
    intro previous
    change _root_.Hypostructure.CT9.localCheckBound
        (Core.Residual.residualOf previous).items
        boolLabels.toEnumeration <= 8
    rw [(Core.Residual.residualOf previous).items_eq]
    decide

def residual (scenario : Scenario) : Residual where
  scenario := scenario
  items := threeItems
  items_eq := rfl

def previous (scenario : Scenario) : Previous :=
  Core.Residual.Ledger.initial (residual scenario)

def overloadedResult : _root_.Hypostructure.CT9.ExecutionResult spec capability :=
  _root_.Hypostructure.CT9.execute spec capability (previous .overloaded)

def boundedResult : _root_.Hypostructure.CT9.ExecutionResult spec capability :=
  _root_.Hypostructure.CT9.execute spec capability (previous .bounded)

theorem overloaded_previous :
    overloadedResult.stage.previous = previous .overloaded := rfl

theorem bounded_previous :
    boundedResult.stage.previous = previous .bounded := rfl

theorem overloaded_terminal : overloadedResult.terminal = .overloaded := by
  decide

theorem bounded_terminal : boundedResult.terminal = .bounded := by
  decide

theorem overloaded_checks : overloadedResult.checks = 4 := by
  decide

theorem bounded_checks : boundedResult.checks = 8 := by
  decide

theorem overloaded_trace :
    overloadedResult.traceNodes =
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .overloadedTerminal] := by
  decide

theorem bounded_trace :
    boundedResult.traceNodes =
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .boundedTerminal] := by
  decide

/-- The first declared label is already overloaded. -/
theorem first_overload_index :
    (_root_.Hypostructure.CT9.overloadScan capability
      (previous .overloaded)
      (_root_.Hypostructure.CT9.computePartition capability
        (previous .overloaded))).index? = some 0 := by
  decide

theorem overloaded_false_count :
    _root_.Hypostructure.CT9.fibreCount capability
      (previous .overloaded) false = 3 := by
  decide

theorem bounded_false_count :
    _root_.Hypostructure.CT9.fibreCount capability
      (previous .bounded) false = 2 := by
  decide

theorem bounded_true_count :
    _root_.Hypostructure.CT9.fibreCount capability
      (previous .bounded) true = 1 := by
  decide

theorem overloaded_total_capacity :
    _root_.Hypostructure.CT9.totalCapacity capability
      (previous .overloaded) = 2 := by
  decide

theorem exact_partition_cardinality :
    (capability.itemsAt (previous .bounded)).card =
      ((capability.labelScheduleAt (previous .bounded)).values.map
        (_root_.Hypostructure.CT9.fibreCount capability
          (previous .bounded))).sum :=
  _root_.Hypostructure.CT9.cardinality_eq_sum_fibreCount

def forcedOverload :=
  _root_.Hypostructure.CT9.runOverloadedOfTotalCapacityLtCardinality spec
    capability (previous .overloaded) (by decide)

def forcedPair := forcedOverload.sameLabelPairOfCapacityOne (by
  intro label
  cases label <;> rfl)

theorem forced_terminal : forcedOverload.result.terminal = .overloaded :=
  forcedOverload.terminal_eq

theorem forced_pair_first : forcedPair.first = 0 := rfl

theorem forced_pair_second : forcedPair.second = 1 := rfl

theorem forced_pair_distinct : forcedPair.first ≠ forcedPair.second :=
  forcedPair.distinct

theorem overloaded_sound :
    _root_.Hypostructure.CT9.OutcomeClaim overloadedResult.outcome :=
  overloadedResult.verified

theorem bounded_sound :
    _root_.Hypostructure.CT9.OutcomeClaim boundedResult.outcome :=
  boundedResult.verified

theorem overloaded_totality :
    Exists fun result : _root_.Hypostructure.CT9.ExecutionResult spec capability =>
      result.stage.previous = previous .overloaded ∧
      _root_.Hypostructure.CT9.OutcomeClaim result.outcome ∧
      result.traceNodes =
        _root_.Hypostructure.CT9.Trace.expectedNodes result.terminal ∧
      result.checks <= capability.workCoefficient *
        (capability.inputSize (previous .overloaded) + 1) ^
          capability.workDegree :=
  _root_.Hypostructure.CT9.run_total spec capability (previous .overloaded)

theorem bounded_deterministic :
    _root_.Hypostructure.CT9.run spec capability (previous .bounded) =
      _root_.Hypostructure.CT9.run spec capability (previous .bounded) :=
  _root_.Hypostructure.CT9.run_deterministic spec capability
    (previous .bounded) _ _ rfl rfl

theorem overloaded_polynomial_work :
    overloadedResult.checks <= capability.workCoefficient *
      (capability.inputSize (previous .overloaded) + 1) ^
        capability.workDegree :=
  overloadedResult.checks_le_polynomial

theorem bounded_polynomial_work :
    boundedResult.checks <= capability.workCoefficient *
      (capability.inputSize (previous .bounded) + 1) ^
        capability.workDegree :=
  boundedResult.checks_le_polynomial

end Neutral

namespace Parity

abbrev profile : _root_.Hypostructure.CT9.ParityCapacityOneProfile
    Neutral.Previous where
  Item := fun _previous => Fin 3
  rank := fun _previous item => item.val
  items := Neutral.itemQuery
  inputSize := fun _previous => 0
  workCoefficient := 8
  workDegree := 0
  workBound := by
    intro previous
    change _root_.Hypostructure.CT9.localCheckBound
        (Core.Residual.residualOf previous).items
        _root_.Hypostructure.CT9.parityLabels.toEnumeration <= 8
    rw [(Core.Residual.residualOf previous).items_eq]
    decide

def run :=
  _root_.Hypostructure.CT9.runParityCapacityOneOfThreeLeCardinality
    profile (Neutral.previous .overloaded) (by decide)

theorem total_capacity :
    _root_.Hypostructure.CT9.totalCapacity profile.capability
      (Neutral.previous .overloaded) = 2 :=
  _root_.Hypostructure.CT9.totalCapacity_parityCapacityOne _ _

theorem terminal : run.result.terminal = .overloaded := run.terminal_eq

theorem trace :
    run.result.traceNodes =
      [.entry, .itemSchedule, .labelSchedule, .partition, .overloadSearch,
        .overloadedTerminal] :=
  run.trace_eq

theorem pair_first : run.pair.first = 0 := rfl

theorem pair_second : run.pair.second = 2 := rfl

theorem pair_distinct : run.pair.first ≠ run.pair.second :=
  run.pair.distinct

theorem pair_same_parity :
    profile.rank (Neutral.previous .overloaded) run.pair.first % 2 =
      profile.rank (Neutral.previous .overloaded) run.pair.second % 2 :=
  run.pair.same_parity

end Parity

namespace GraphAdapter

def object : Graph.FiniteObject where
  Vertex := Fin 1
  graph := ⊥
  vertices := inferInstance
  decideAdj := inferInstance

def objectQuery : Core.Residual.Query Neutral.Previous fun _previous =>
    Graph.FiniteObject :=
  Neutral.residualQuery.map fun _previous _residual => object

def spec := Graph.CT9.roleSpec objectQuery
  (fun _previous => Fin 3) (fun _previous => Bool)
  (fun previous _object item => Neutral.itemLabel previous item)
  (fun previous _object label => Neutral.labelCapacity previous label)

def capability := Graph.CT9.roleCapability objectQuery
  (fun _previous => Fin 3) (fun _previous => Bool)
  (fun previous _object item => Neutral.itemLabel previous item)
  (fun previous _object label => Neutral.labelCapacity previous label)
  Neutral.itemQuery (fun _previous => Neutral.boolLabels)
  (fun _previous => 0) 8 0 (by
    intro previous
    change _root_.Hypostructure.CT9.localCheckBound
        (Core.Residual.residualOf previous).items
        Neutral.boolLabels.toEnumeration <= 8
    rw [(Core.Residual.residualOf previous).items_eq]
    decide)

def result := _root_.Hypostructure.CT9.execute spec capability
  (Neutral.previous .bounded)

theorem terminal : result.terminal = .bounded := by decide

theorem checks : result.checks = 8 := by decide

theorem sound : _root_.Hypostructure.CT9.OutcomeClaim result.outcome :=
  result.verified

end GraphAdapter

namespace PDEAdapter

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
  nested_trans := fun _smallLarge _largeOuter => trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Unit
  restrict := fun _state _window => ()
  restrictLocal := fun _nested object => object
  restrict_refl := fun _window _object => rfl
  restrict_trans := fun _smallLarge _largeOuter _object => rfl
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

def stateQuery : Core.Residual.Query Neutral.Previous fun _previous =>
    model.problem.Ambient :=
  Neutral.residualQuery.map fun _previous _residual => ()

def spec := PDE.CT9.packetSpec model stateQuery
  (fun _previous => Fin 3) (fun _previous => Bool)
  (fun previous _state item => Neutral.itemLabel previous item)
  (fun previous _state label => Neutral.labelCapacity previous label)

def capability := PDE.CT9.packetCapability model stateQuery
  (fun _previous => Fin 3) (fun _previous => Bool)
  (fun previous _state item => Neutral.itemLabel previous item)
  (fun previous _state label => Neutral.labelCapacity previous label)
  Neutral.itemQuery (fun _previous => Neutral.boolLabels)
  (fun _previous => 0) 8 0 (by
    intro previous
    change _root_.Hypostructure.CT9.localCheckBound
        (Core.Residual.residualOf previous).items
        Neutral.boolLabels.toEnumeration <= 8
    rw [(Core.Residual.residualOf previous).items_eq]
    decide)

def result := _root_.Hypostructure.CT9.execute spec capability
  (Neutral.previous .overloaded)

theorem terminal : result.terminal = .overloaded := by decide

theorem checks : result.checks = 4 := by decide

theorem sound : _root_.Hypostructure.CT9.OutcomeClaim result.outcome :=
  result.verified

end PDEAdapter

#print axioms Neutral.overloaded_sound
#print axioms Neutral.bounded_sound
#print axioms Neutral.overloaded_totality
#print axioms Neutral.bounded_deterministic
#print axioms Neutral.exact_partition_cardinality
#print axioms Neutral.forced_pair_distinct
#print axioms Parity.pair_same_parity
#print axioms GraphAdapter.sound
#print axioms PDEAdapter.sound

end Hypostructure.Fixtures.CT9
