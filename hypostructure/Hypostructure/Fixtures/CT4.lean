import Hypostructure.Graph.CT4
import Hypostructure.PDE.CT4

/-!
# CT4 vertical-slice fixtures

The neutral fixture exercises all four terminals over schedules stored in the
root residual.  Additional fixtures validate functional cardinality, graph
vertex charging, and PDE window charging without application-owned routes.
-/

namespace Hypostructure.Fixtures.CT4

namespace Neutral

inductive Mode where
  | missing
  | overloaded
  | c4
  | capacity
  deriving DecidableEq, Repr

structure Residual where
  mode : Mode
  demands : Core.Finite.Enumeration Bool
  payers : Core.Finite.Enumeration Bool

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def demandQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.demands

def payerQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.payers

def eligible (previous : Previous) (demand payer : Bool) : Prop :=
  match (Core.Residual.residualOf previous).mode with
  | .missing => False
  | .overloaded => payer = false
  | .c4 => payer = demand
  | .capacity => payer = demand

def weight (_previous : Previous) (_demand : Bool) : Nat := 1

def payerCapacity (previous : Previous) (payer : Bool) : Nat :=
  match (Core.Residual.residualOf previous).mode with
  | .missing => 0
  | .overloaded => if payer then 0 else 1
  | .c4 => 1
  | .capacity => 1

def required (previous : Previous) : Nat :=
  match (Core.Residual.residualOf previous).mode with
  | .missing => 0
  | .overloaded => 0
  | .c4 => 3
  | .capacity => 1

def spec : _root_.Hypostructure.CT4.Spec Previous where
  Demand := fun _previous => Bool
  Payer := fun _previous => Bool
  Eligible := eligible
  demandWeight := weight
  capacity := payerCapacity
  required := required

def eligibleDecidable (previous : Previous) (demand payer : Bool) :
    Decidable (spec.Eligible previous demand payer) := by
  change Decidable (eligible previous demand payer)
  unfold eligible
  split <;> infer_instance

def capability : _root_.Hypostructure.CT4.Capability spec where
  demands := demandQuery
  payers := payerQuery
  eligibleDecidable := eligibleDecidable
  inputSize := fun previous =>
    _root_.Hypostructure.CT4.localCheckBound
      (demandQuery.read previous) (payerQuery.read previous)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    change _root_.Hypostructure.CT4.localCheckBound
        (demandQuery.read previous) (payerQuery.read previous) <=
      1 * (_root_.Hypostructure.CT4.localCheckBound
        (demandQuery.read previous) (payerQuery.read previous) + 1) ^ 1
    simp only [one_mul, Nat.pow_one]
    omega

def boolSchedule : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

def residual (mode : Mode) : Residual where
  mode := mode
  demands := boolSchedule
  payers := boolSchedule

def previous (mode : Mode) : Previous :=
  Core.Residual.Ledger.initial (residual mode)

def missingResult : _root_.Hypostructure.CT4.ExecutionResult spec capability :=
  _root_.Hypostructure.CT4.execute spec capability (previous .missing)

def overloadResult : _root_.Hypostructure.CT4.ExecutionResult spec capability :=
  _root_.Hypostructure.CT4.execute spec capability (previous .overloaded)

def c4Result : _root_.Hypostructure.CT4.ExecutionResult spec capability :=
  _root_.Hypostructure.CT4.execute spec capability (previous .c4)

def capacityResult : _root_.Hypostructure.CT4.ExecutionResult spec capability :=
  _root_.Hypostructure.CT4.execute spec capability (previous .capacity)

theorem missing_previous :
    missingResult.stage.previous = previous .missing := rfl

theorem overload_previous :
    overloadResult.stage.previous = previous .overloaded := rfl

theorem c4_previous : c4Result.stage.previous = previous .c4 := rfl

theorem capacity_previous :
    capacityResult.stage.previous = previous .capacity := rfl

theorem missing_terminal : missingResult.terminal = .missingPayer := by decide

theorem overload_terminal :
    overloadResult.terminal = .overloadedFibre := by decide

theorem c4_terminal : c4Result.terminal = .c4 := by decide

theorem capacity_terminal : capacityResult.terminal = .capacity := by decide

theorem missing_checks : missingResult.checks = 5 := by decide

theorem overload_checks : overloadResult.checks = 7 := by decide

theorem c4_checks : c4Result.checks = 12 := by decide

theorem capacity_checks : capacityResult.checks = 12 := by decide

theorem missing_trace : missingResult.traceNodes =
    [.entry, .assignment, .availabilitySearch, .missingPayerTerminal] :=
  by decide

theorem overload_trace : overloadResult.traceNodes =
    [.entry, .assignment, .availabilitySearch, .fibreComputation,
      .overloadSearch, .overloadedFibreTerminal] :=
  by decide

theorem c4_trace : c4Result.traceNodes =
    [.entry, .assignment, .availabilitySearch, .fibreComputation,
      .overloadSearch, .capacityComparison, .c4Terminal] :=
  by decide

theorem capacity_trace : capacityResult.traceNodes =
    [.entry, .assignment, .availabilitySearch, .fibreComputation,
      .overloadSearch, .capacityComparison, .capacityTerminal] :=
  by decide

theorem missing_sound :
    _root_.Hypostructure.CT4.OutcomeClaim missingResult.outcome :=
  missingResult.verified

theorem overload_sound :
    _root_.Hypostructure.CT4.OutcomeClaim overloadResult.outcome :=
  overloadResult.verified

theorem c4_sound :
    _root_.Hypostructure.CT4.OutcomeClaim c4Result.outcome :=
  c4Result.verified

theorem capacity_sound :
    _root_.Hypostructure.CT4.OutcomeClaim capacityResult.outcome :=
  capacityResult.verified

theorem missing_work : missingResult.checks <=
    capability.workCoefficient *
      (capability.inputSize (previous .missing) + 1) ^
        capability.workDegree :=
  missingResult.checks_le_polynomial

theorem overload_work : overloadResult.checks <=
    capability.workCoefficient *
      (capability.inputSize (previous .overloaded) + 1) ^
        capability.workDegree :=
  overloadResult.checks_le_polynomial

theorem c4_work : c4Result.checks <= capability.workCoefficient *
    (capability.inputSize (previous .c4) + 1) ^ capability.workDegree :=
  c4Result.checks_le_polynomial

theorem capacity_work : capacityResult.checks <=
    capability.workCoefficient *
      (capability.inputSize (previous .capacity) + 1) ^
        capability.workDegree :=
  capacityResult.checks_le_polynomial

end Neutral

namespace Functional

structure Residual where
  demands : Core.Finite.Enumeration (Fin 3)
  payers : Core.Finite.Enumeration Bool

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def profile : _root_.Hypostructure.CT4.FunctionalCardinalityProfile Previous where
  Demand := fun _previous => Fin 3
  Payer := fun _previous => Bool
  Eligible := fun _previous demand payer =>
    demand.1 = if payer then 1 else 0
  demands := residualQuery.map fun _previous residual => residual.demands
  payers := residualQuery.map fun _previous residual => residual.payers
  eligibleDecidable := fun _previous _demand _payer => inferInstance
  functional := by
    intro _previous payer left right leftEligible rightEligible
    apply Fin.ext
    exact leftEligible.trans rightEligible.symm
  inputSize := fun previous =>
    _root_.Hypostructure.CT4.localCheckBound
      ((residualQuery.map fun _previous residual => residual.demands).read
        previous)
      ((residualQuery.map fun _previous residual => residual.payers).read
        previous)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    change _root_.Hypostructure.CT4.localCheckBound
        ((residualQuery.map fun _previous residual => residual.demands).read
          previous)
        ((residualQuery.map fun _previous residual => residual.payers).read
          previous) <=
      1 * (_root_.Hypostructure.CT4.localCheckBound
        ((residualQuery.map fun _previous residual => residual.demands).read
          previous)
        ((residualQuery.map fun _previous residual => residual.payers).read
          previous) + 1) ^ 1
    simp only [one_mul, Nat.pow_one]
    omega

def residual : Residual where
  demands := Core.Finite.Enumeration.ofFinEnum inferInstance
  payers := Neutral.boolSchedule

def previous : Previous := Core.Residual.Ledger.initial residual

def result := profile.run previous

theorem terminal : result.terminal = .missingPayer := by
  apply profile.run_terminal_eq_missing
  decide

def missing : _root_.Hypostructure.CT4.MissingCertificate
    profile.capability previous :=
  profile.missingCertificate previous (by decide)

theorem missing_is_two : missing.demand = (2 : Fin 3) := by
  have falseMember : false ∈
      (profile.capability.payersAt previous).values := by
    change false ∈ Neutral.boolSchedule.values
    decide
  have trueMember : true ∈
      (profile.capability.payersAt previous).values := by
    change true ∈ Neutral.boolSchedule.values
    decide
  have noFalse := missing.noEligible false falseMember
  have noTrue := missing.noEligible true trueMember
  have notZero : missing.demand.1 ≠ 0 := by
    intro equal
    apply noFalse
    change missing.demand.1 = 0
    exact equal
  have notOne : missing.demand.1 ≠ 1 := by
    intro equal
    apply noTrue
    change missing.demand.1 = 1
    exact equal
  apply Fin.ext
  omega

theorem missing_has_no_payer : forall payer,
    payer ∈ (profile.payers.read previous).values ->
      Not (profile.Eligible previous missing.demand payer) :=
  missing.noEligible

end Functional

namespace GraphVertex

abbrev Vertex := Fin 2

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

structure Residual where
  selected : Graph.FiniteObject
  demands : Core.Finite.Enumeration (Fin 2)

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  residualQuery.map fun _previous residual => residual.selected

def demandQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 2) :=
  residualQuery.map fun _previous residual => residual.demands

abbrev Demand (_previous : Previous) := Fin 2

def Eligible (_previous : Previous) (selected : Graph.FiniteObject)
    (_demand : Fin 2) (_payer : selected.Vertex) : Prop :=
  True

def demandWeight (_previous : Previous) (_selected : Graph.FiniteObject)
    (_demand : Fin 2) : Nat := 1

def capacity (_previous : Previous) (selected : Graph.FiniteObject)
    (_payer : selected.Vertex) : Nat := 0

def required (_previous : Previous) (_selected : Graph.FiniteObject) : Nat := 0

def spec := Graph.CT4.vertexChargingSpec objectQuery Demand Eligible
  demandWeight capacity required

def capability := Graph.CT4.vertexChargingCapability objectQuery Demand Eligible
  demandWeight capacity required demandQuery
  (fun _previous _selected _demand _payer => .isTrue trivial)
  (fun previous => _root_.Hypostructure.CT4.localCheckBound
    (demandQuery.read previous) (Graph.CT4.vertexPayers objectQuery |>.read previous))
  1 1 (by
    intro previous
    simp only [one_mul, Nat.pow_one]
    omega)

def residual : Residual where
  selected := object
  demands := Core.Finite.Enumeration.ofFinEnum inferInstance

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT4.ExecutionResult spec capability :=
  _root_.Hypostructure.CT4.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem terminal : result.terminal = .overloadedFibre := by decide

theorem exact_checks : result.checks = 7 := by decide

theorem sound : _root_.Hypostructure.CT4.OutcomeClaim result.outcome :=
  result.verified

end GraphVertex

namespace PDEWindow

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _state => True
  BranchState := fun _state => Unit

def atlas : PDE.LocalAtlas problem where
  Point := Unit
  Window := Bool
  contains := fun _point _window => True
  nested := fun _small _large => True
  nested_refl := fun _window => trivial
  nested_trans := fun _firstSecond _secondThird => trivial
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
  demands : Core.Finite.Enumeration (Fin 2)
  windows : Core.Finite.Enumeration Bool

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def stateQuery : Core.Residual.Query Previous fun _previous =>
    model.problem.Ambient :=
  residualQuery.map fun _previous residual => residual.state

def demandQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 2) :=
  residualQuery.map fun _previous residual => residual.demands

def windowQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration model.atlas.Window :=
  residualQuery.map fun _previous residual => residual.windows

abbrev Demand (_previous : Previous) := Fin 2

def Eligible (_previous : Previous) (_state : model.problem.Ambient)
    (_demand : Fin 2) (_window : model.atlas.Window) : Prop :=
  True

def demandWeight (_previous : Previous) (_state : model.problem.Ambient)
    (_demand : Fin 2) : Nat := 1

def capacity (_previous : Previous) (_state : model.problem.Ambient)
    (_window : model.atlas.Window) : Nat := 2

def required (_previous : Previous) (_state : model.problem.Ambient) : Nat := 2

def spec := PDE.CT4.windowChargingSpec model stateQuery Demand Eligible
  demandWeight capacity required

def capability := PDE.CT4.windowChargingCapability model stateQuery Demand
  Eligible demandWeight capacity required demandQuery windowQuery
  (fun _previous _state _demand _window => .isTrue trivial)
  (fun previous => _root_.Hypostructure.CT4.localCheckBound
    (demandQuery.read previous) (windowQuery.read previous))
  1 1 (by
    intro previous
    simp only [one_mul, Nat.pow_one]
    omega)

def residual : Residual where
  state := ()
  demands := Core.Finite.Enumeration.ofFinEnum inferInstance
  windows := Neutral.boolSchedule

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT4.ExecutionResult spec capability :=
  _root_.Hypostructure.CT4.execute spec capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem terminal : result.terminal = .capacity := by decide

theorem exact_checks : result.checks = 11 := by decide

theorem sound : _root_.Hypostructure.CT4.OutcomeClaim result.outcome :=
  result.verified

end PDEWindow

end Hypostructure.Fixtures.CT4
