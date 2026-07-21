import Hypostructure.Graph.CT17
import Hypostructure.PDE.CT17

/-!
# CT17 vertical-slice fixtures

The neutral fixture exercises every terminal, exact trace, exact branch work,
and both finite-scale boundaries.  Graph and PDE fixtures verify that their
adapters merely instantiate the same residual-owned executor.
-/

namespace Hypostructure.Fixtures.CT17

namespace Neutral

inductive Mode where
  | incompatible
  | exhausted
  | survivors
  | targetHit
  | orbit
  deriving DecidableEq, Repr

def boolSchedule : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

def scaleSchedule : Core.Finite.Enumeration Nat :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

def scaleFor : Mode -> Nat
  | .incompatible => 0
  | .exhausted => 0
  | .survivors => 1
  | .targetHit => 2
  | .orbit => 2

structure Residual where
  mode : Mode
  targets : Core.Finite.Enumeration Bool
  offsets : Core.Finite.Enumeration Bool
  scales : Core.Finite.Enumeration Nat
  positions : Core.Finite.Enumeration Bool
  selectedScale : Nat
  selectedScale_mem : selectedScale ∈ scales.values
  finiteScaleLimit : Nat

abbrev Previous := Core.Residual.Ledger Residual

def residual (mode : Mode) : Residual where
  mode := mode
  targets := boolSchedule
  offsets := boolSchedule
  scales := scaleSchedule
  positions := boolSchedule
  selectedScale := scaleFor mode
  selectedScale_mem := by cases mode <;> decide
  finiteScaleLimit := 1

def previous (mode : Mode) : Previous :=
  Core.Residual.Ledger.initial (residual mode)

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def targetQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.targets

def offsetQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.offsets

def scaleQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Nat :=
  residualQuery.map fun _previous inherited => inherited.scales

def selectedScaleQuery : Core.Residual.Query Previous fun _previous => Nat :=
  residualQuery.map fun _previous inherited => inherited.selectedScale

def positionQuery (_scale : Nat) :
    Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.positions

def scaleLimitQuery : Core.Residual.Query Previous fun _previous => Nat :=
  residualQuery.map fun _previous inherited => inherited.finiteScaleLimit

def modeAt (previous : Previous) : Mode :=
  (Core.Residual.residualOf previous).mode

def spec : _root_.Hypostructure.CT17.Spec Previous where
  Target := fun _previous => Bool
  Offset := fun _previous => Bool
  Position := fun _previous _scale => Bool
  Value := fun _previous => Nat
  targetValue := fun _previous target => if target then 10 else 0
  blockValue := fun previous _scale position _offset =>
    match modeAt previous with
    | .survivors => if position then 99 else 0
    | _mode => 0
  orbitValue := fun previous _scale offset =>
    match modeAt previous with
    | .orbit => if offset then 100 else 99
    | _mode => 0
  Compatible := fun previous _target _offset =>
    modeAt previous ≠ .incompatible

def localSize (previous : Previous) : Nat :=
  _root_.Hypostructure.CT17.localCheckBound
    (targetQuery.read previous) (offsetQuery.read previous)
    ((positionQuery (selectedScaleQuery.read previous)).read previous)

def capability : _root_.Hypostructure.CT17.Capability spec where
  targets := targetQuery
  offsets := offsetQuery
  scales := scaleQuery
  selectedScale := selectedScaleQuery
  selectedScale_mem := fun previous =>
    (Core.Residual.residualOf previous).selectedScale_mem
  positions := positionQuery
  finiteScaleLimit := scaleLimitQuery
  compatibleDecidable := fun previous _target _offset => by
    unfold spec
    exact inferInstance
  valueDecidableEq := by
    intro _previous
    change DecidableEq Nat
    infer_instance
  inputSize := localSize
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    change localSize previous <= 1 * (localSize previous + 1) ^ 1
    simp

def incompatibleResult :
    _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability (previous .incompatible)

def exhaustedResult :
    _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability (previous .exhausted)

def survivorResult :
    _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability (previous .survivors)

def targetHitResult :
    _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability (previous .targetHit)

def orbitResult :
    _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability (previous .orbit)

theorem incompatible_previous :
    incompatibleResult.stage.previous = previous .incompatible := rfl

theorem exhausted_previous :
    exhaustedResult.stage.previous = previous .exhausted := rfl

theorem survivor_previous :
    survivorResult.stage.previous = previous .survivors := rfl

theorem target_hit_previous :
    targetHitResult.stage.previous = previous .targetHit := rfl

theorem orbit_previous :
    orbitResult.stage.previous = previous .orbit := rfl

theorem incompatible_terminal :
    incompatibleResult.terminal = .incompatibility := rfl

theorem exhausted_terminal : exhaustedResult.terminal = .exhausted := rfl

theorem survivor_terminal : survivorResult.terminal = .survivors := rfl

theorem target_hit_terminal : targetHitResult.terminal = .targetHit := rfl

theorem orbit_terminal : orbitResult.terminal = .orbit := rfl

theorem incompatible_checks : incompatibleResult.checks = 1 := rfl

theorem exhausted_checks : exhaustedResult.checks = 8 := rfl

theorem survivor_checks : survivorResult.checks = 11 := rfl

theorem target_hit_checks : targetHitResult.checks = 6 := rfl

theorem orbit_checks : orbitResult.checks = 11 := rfl

theorem incompatible_trace : incompatibleResult.traceNodes =
    [.entry, .inheritedSchedules, .admissibilityScan,
      .incompatibilityTerminal] := rfl

theorem exhausted_trace : exhaustedResult.traceNodes =
    [.entry, .inheritedSchedules, .admissibilityScan, .scaleDecision,
      .survivorEnumeration, .survivorDecision, .exhaustedTerminal] := rfl

theorem survivor_trace : survivorResult.traceNodes =
    [.entry, .inheritedSchedules, .admissibilityScan, .scaleDecision,
      .survivorEnumeration, .survivorDecision, .survivorTerminal] := rfl

theorem target_hit_trace : targetHitResult.traceNodes =
    [.entry, .inheritedSchedules, .admissibilityScan, .scaleDecision,
      .orbitArithmetic, .targetHitTerminal] := rfl

theorem orbit_trace : orbitResult.traceNodes =
    [.entry, .inheritedSchedules, .admissibilityScan, .scaleDecision,
      .orbitArithmetic, .orbitTerminal] := rfl

theorem exhausted_survivor_list :
    _root_.Hypostructure.CT17.survivorList capability
      (previous .exhausted) = [] := rfl

theorem survivor_list :
    _root_.Hypostructure.CT17.survivorList capability
      (previous .survivors) = [true] := rfl

theorem orbit_values :
    (offsetQuery.read (previous .orbit)).values.map
        (fun offset => if offset then 100 else 99) =
      ([99, 100] : List Nat) := rfl

/-- Scale zero exercises the lower finite boundary. -/
theorem exhausted_scale_zero :
    capability.scaleAt (previous .exhausted) = 0 := rfl

/-- Scale one exercises the declared maximum finite scale. -/
theorem survivor_scale_is_limit :
    capability.scaleAt (previous .survivors) =
      capability.scaleLimitAt (previous .survivors) := rfl

/-- Scale two exercises the first strict orbit scale. -/
theorem orbit_scale_above_limit :
    capability.scaleLimitAt (previous .orbit) <
      capability.scaleAt (previous .orbit) := by decide

theorem incompatible_verified :
    _root_.Hypostructure.CT17.OutcomeClaim incompatibleResult.outcome :=
  incompatibleResult.verified

theorem exhausted_verified :
    _root_.Hypostructure.CT17.OutcomeClaim exhaustedResult.outcome :=
  exhaustedResult.verified

theorem survivor_verified :
    _root_.Hypostructure.CT17.OutcomeClaim survivorResult.outcome :=
  survivorResult.verified

theorem target_hit_verified :
    _root_.Hypostructure.CT17.OutcomeClaim targetHitResult.outcome :=
  targetHitResult.verified

theorem orbit_verified :
    _root_.Hypostructure.CT17.OutcomeClaim orbitResult.outcome :=
  orbitResult.verified

theorem orbit_work_bound : orbitResult.checks <=
    capability.workCoefficient *
      (capability.inputSize orbitResult.stage.previous + 1) ^
        capability.workDegree :=
  orbitResult.checks_le_polynomial

end Neutral

namespace GraphBoundedTarget

abbrev Vertex := Fin 2

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

structure Residual where
  object : Graph.FiniteObject
  targets : Core.Finite.Enumeration Bool
  offsets : Core.Finite.Enumeration Bool
  scales : Core.Finite.Enumeration Nat
  positions : Core.Finite.Enumeration Bool
  scale : Nat
  scale_mem : scale ∈ scales.values
  limit : Nat

abbrev Previous := Core.Residual.Ledger Residual

def residual : Residual where
  object := object
  targets := Neutral.boolSchedule
  offsets := Neutral.boolSchedule
  scales := Neutral.scaleSchedule
  positions := Neutral.boolSchedule
  scale := 1
  scale_mem := by decide
  limit := 1

def previous : Previous := Core.Residual.Ledger.initial residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  residualQuery.map fun _previous inherited => inherited.object

def targets : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.targets

def offsets : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.offsets

def scales : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Nat :=
  residualQuery.map fun _previous inherited => inherited.scales

def selectedScale : Core.Residual.Query Previous fun _previous => Nat :=
  residualQuery.map fun _previous inherited => inherited.scale

def positions (_scale : Nat) : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.positions

def limit : Core.Residual.Query Previous fun _previous => Nat :=
  residualQuery.map fun _previous inherited => inherited.limit

def targetValue (_previous : Previous) (selected : Graph.FiniteObject)
    (target : Bool) : Nat :=
  if target then selected.vertices.card + 1 else selected.vertices.card

def blockValue (_previous : Previous) (selected : Graph.FiniteObject)
    (_scale : Nat) (position : Bool) (_offset : Bool) : Nat :=
  if position then 99 else selected.vertices.card

def orbitValue (_previous : Previous) (_selected : Graph.FiniteObject)
    (_scale : Nat) (_offset : Bool) : Nat := 99

def compatible (_previous : Previous) (_selected : Graph.FiniteObject)
    (_target _offset : Bool) : Prop := True

def spec := Graph.CT17.boundedTargetSpec objectQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _scale => Bool) (fun _previous => Nat)
  targetValue blockValue orbitValue compatible

def localSize (previous : Previous) : Nat :=
  _root_.Hypostructure.CT17.localCheckBound
    (targets.read previous) (offsets.read previous)
    ((positions (selectedScale.read previous)).read previous)

def capability := Graph.CT17.boundedTargetCapability objectQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _scale => Bool) (fun _previous => Nat)
  targetValue blockValue orbitValue compatible targets offsets scales
  selectedScale
  (fun previous => (Core.Residual.residualOf previous).scale_mem)
  positions limit
  (fun _previous _selected _target _offset => .isTrue trivial)
  (fun _previous => inferInstance) localSize 1 1 (by
    intro selected
    simp only [localSize, one_mul, pow_one]
    omega)

def result : _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .survivors := rfl

theorem result_checks : result.checks = 11 := rfl

theorem result_verified :
    _root_.Hypostructure.CT17.OutcomeClaim result.outcome :=
  result.verified

end GraphBoundedTarget

namespace PDEBoundedScale

def problem : Core.Problem where
  Ambient := Bool
  Baseline := fun _object => True
  BranchState := fun _object => Unit

def atlas : PDE.LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _point _window => True
  nested := fun _small _large => True
  nested_refl := fun _window => trivial
  nested_trans := fun _smallLarge _largeOuter => trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Bool
  restrict := fun object _window => object
  restrictLocal := fun _nested object => object
  restrict_refl := fun _window _object => rfl
  restrict_trans := fun _smallLarge _largeOuter _object => rfl
  restrict_global := by
    intro object small large nested
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
  state : Bool
  targets : Core.Finite.Enumeration Bool
  offsets : Core.Finite.Enumeration Bool
  scales : Core.Finite.Enumeration Nat
  positions : Core.Finite.Enumeration Bool
  scale : Nat
  scale_mem : scale ∈ scales.values
  limit : Nat

abbrev Previous := Core.Residual.Ledger Residual

def residual : Residual where
  state := true
  targets := Neutral.boolSchedule
  offsets := Neutral.boolSchedule
  scales := Neutral.scaleSchedule
  positions := Neutral.boolSchedule
  scale := 2
  scale_mem := by decide
  limit := 1

def previous : Previous := Core.Residual.Ledger.initial residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def stateQuery : Core.Residual.Query Previous fun _previous => Bool :=
  residualQuery.map fun _previous inherited => inherited.state

def targets : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.targets

def offsets : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.offsets

def scales : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Nat :=
  residualQuery.map fun _previous inherited => inherited.scales

def selectedScale : Core.Residual.Query Previous fun _previous => Nat :=
  residualQuery.map fun _previous inherited => inherited.scale

def positions (_scale : Nat) : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous inherited => inherited.positions

def limit : Core.Residual.Query Previous fun _previous => Nat :=
  residualQuery.map fun _previous inherited => inherited.limit

def targetValue (_previous : Previous) (_state : Bool)
    (target : Bool) : Nat :=
  if target then 10 else 0

def blockValue (_previous : Previous) (_state : Bool) (_scale : Nat)
    (_position _offset : Bool) : Nat := 0

def orbitValue (_previous : Previous) (_state : Bool) (_scale : Nat)
    (offset : Bool) : Nat :=
  if offset then 100 else 99

def compatible (_previous : Previous) (state : Bool)
    (_target _offset : Bool) : Prop :=
  state = true

def spec := PDE.CT17.boundedScaleSpec model stateQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _scale => Bool) (fun _previous => Nat)
  targetValue blockValue orbitValue compatible

def localSize (previous : Previous) : Nat :=
  _root_.Hypostructure.CT17.localCheckBound
    (targets.read previous) (offsets.read previous)
    ((positions (selectedScale.read previous)).read previous)

def capability := PDE.CT17.boundedScaleCapability model stateQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _scale => Bool) (fun _previous => Nat)
  targetValue blockValue orbitValue compatible targets offsets scales
  selectedScale
  (fun previous => (Core.Residual.residualOf previous).scale_mem)
  positions limit
  (fun _previous state _target _offset => Bool.decEq state true)
  (fun _previous => inferInstance) localSize 1 1 (by
    intro selected
    simp only [localSize, one_mul, pow_one]
    omega)

def result : _root_.Hypostructure.CT17.ExecutionResult spec capability :=
  _root_.Hypostructure.CT17.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .orbit := rfl

theorem result_checks : result.checks = 11 := rfl

theorem result_verified :
    _root_.Hypostructure.CT17.OutcomeClaim result.outcome :=
  result.verified

end PDEBoundedScale

#print axioms Neutral.incompatible_terminal
#print axioms Neutral.incompatible_checks
#print axioms Neutral.incompatible_verified
#print axioms Neutral.exhausted_terminal
#print axioms Neutral.exhausted_checks
#print axioms Neutral.exhausted_verified
#print axioms Neutral.survivor_terminal
#print axioms Neutral.survivor_checks
#print axioms Neutral.survivor_verified
#print axioms Neutral.target_hit_terminal
#print axioms Neutral.target_hit_checks
#print axioms Neutral.target_hit_verified
#print axioms Neutral.orbit_terminal
#print axioms Neutral.orbit_checks
#print axioms Neutral.orbit_verified
#print axioms GraphBoundedTarget.result_terminal
#print axioms GraphBoundedTarget.result_verified
#print axioms PDEBoundedScale.result_terminal
#print axioms PDEBoundedScale.result_verified

end Hypostructure.Fixtures.CT17
