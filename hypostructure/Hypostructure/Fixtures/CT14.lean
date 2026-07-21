import Hypostructure.Graph.CT14
import Hypostructure.PDE.CT14

/-!
# CT14 vertical-slice fixtures

One three-member residual reaches every CT14 terminal and exposes exact scan
work.  Thin graph and PDE fixtures instantiate the same machine without
introducing domain-specific outcomes or routing.
-/

namespace Hypostructure.Fixtures.CT14

namespace Neutral

open Hypostructure.Core

inductive Scenario where
  | unboundedMember
  | missingLabel
  | aggregate
  | capacity
  deriving DecidableEq, Repr

def threeMembers : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

/-- The member schedule is literal residual data, together with its local
work certificate. -/
structure Residual where
  scenario : Scenario
  members : Core.Finite.Enumeration (Fin 3)
  work_le_ten : _root_.Hypostructure.CT14.localCheckBound members <= 10

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def memberQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.members

def scenarioAt (previous : Previous) : Scenario :=
  (Core.Residual.residualOf previous).scenario

def memberLowerMass (previous : Previous) (_member : Fin 3) : Nat :=
  match scenarioAt previous with
  | .aggregate => 2
  | _ => 1

def memberCapacity (previous : Previous) (member : Fin 3) : Option Nat :=
  match scenarioAt previous with
  | .unboundedMember => if member = 1 then none else some 2
  | .aggregate => some 1
  | _ => some 2

def memberLabel (previous : Previous) (member : Fin 3) : Option Bool :=
  match scenarioAt previous with
  | .missingLabel => if member = 2 then none else some false
  | _ => if member = 2 then some true else some false

abbrev spec : _root_.Hypostructure.CT14.Spec Previous where
  Member := fun _previous => Fin 3
  Label := fun _previous => Bool
  memberLowerMass := memberLowerMass
  memberCapacity := memberCapacity
  memberLabel := memberLabel

def capability : _root_.Hypostructure.CT14.Capability spec where
  members := memberQuery
  labelDecidableEq := fun _previous => inferInstance
  inputSize := fun _previous => 0
  workCoefficient := 10
  workDegree := 0
  workBound := fun previous => by
    change _root_.Hypostructure.CT14.localCheckBound
      (Core.Residual.residualOf previous).members <= 10
    exact (Core.Residual.residualOf previous).work_le_ten

def residual (scenario : Scenario) : Residual where
  scenario := scenario
  members := threeMembers
  work_le_ten := by decide

def previous (scenario : Scenario) : Previous :=
  Core.Residual.Ledger.initial (residual scenario)

def unboundedResult :=
  _root_.Hypostructure.CT14.execute spec capability
    (previous .unboundedMember)

def missingLabelResult :=
  _root_.Hypostructure.CT14.execute spec capability
    (previous .missingLabel)

def aggregateResult :=
  _root_.Hypostructure.CT14.execute spec capability
    (previous .aggregate)

def capacityResult :=
  _root_.Hypostructure.CT14.execute spec capability
    (previous .capacity)

theorem unbounded_terminal :
    unboundedResult.terminal = .unboundedMember := by decide

theorem missingLabel_terminal :
    missingLabelResult.terminal = .missingLabel := by decide

theorem aggregate_terminal :
    aggregateResult.terminal = .aggregate := by decide

theorem capacity_terminal :
    capacityResult.terminal = .capacity := by decide

theorem unbounded_previous :
    unboundedResult.stage.previous = previous .unboundedMember := rfl

theorem capacity_previous :
    capacityResult.stage.previous = previous .capacity := rfl

/-- The missing capacity is at index one, so the capacity scan pays two. -/
theorem unbounded_capacity_scan_checks :
    (_root_.Hypostructure.CT14.countedCapacityScan capability
      (previous .unboundedMember)).checks = 2 := by decide

/-- The missing-label branch first exhausts all capacities. -/
theorem missing_capacity_scan_checks :
    (_root_.Hypostructure.CT14.countedCapacityScan capability
      (previous .missingLabel)).checks = 3 := by decide

/-- Its first missing label is the final scheduled member. -/
theorem missing_label_scan_checks :
    (_root_.Hypostructure.CT14.countedLabelScan capability
      (previous .missingLabel)).checks = 3 := by decide

theorem unbounded_checks : unboundedResult.checks = 5 := by decide
theorem missingLabel_checks : missingLabelResult.checks = 9 := by decide
theorem aggregate_checks : aggregateResult.checks = 10 := by decide
theorem capacity_checks : capacityResult.checks = 10 := by decide

theorem unbounded_trace :
    unboundedResult.traceNodes =
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .unboundedMemberTerminal] := by decide

theorem missingLabel_trace :
    missingLabelResult.traceNodes =
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .missingLabelTerminal] := by decide

theorem aggregate_trace :
    aggregateResult.traceNodes =
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .aggregateLedger, .aggregateComparison,
        .aggregateTerminal] := by decide

theorem capacity_trace :
    capacityResult.traceNodes =
      [.entry, .memberSchedule, .lowerMassComputation, .capacityScan,
        .labelScan, .aggregateLedger, .aggregateComparison,
        .capacityTerminal] := by decide

theorem aggregate_lower_mass :
    _root_.Hypostructure.CT14.lowerMass capability
      (previous .aggregate) = 6 := by decide

theorem aggregate_upper_capacity :
    _root_.Hypostructure.CT14.upperCapacity capability
      (previous .aggregate) = 3 := by decide

theorem capacity_false_multiplicity :
    _root_.Hypostructure.CT14.multiplicity capability
      (previous .capacity) false = 2 := by decide

theorem capacity_true_multiplicity :
    _root_.Hypostructure.CT14.multiplicity capability
      (previous .capacity) true = 1 := by decide

theorem unbounded_verified :
    _root_.Hypostructure.CT14.OutcomeClaim unboundedResult.outcome :=
  unboundedResult.verified

theorem missingLabel_verified :
    _root_.Hypostructure.CT14.OutcomeClaim missingLabelResult.outcome :=
  missingLabelResult.verified

theorem aggregate_verified :
    _root_.Hypostructure.CT14.OutcomeClaim aggregateResult.outcome :=
  aggregateResult.verified

theorem capacity_verified :
    _root_.Hypostructure.CT14.OutcomeClaim capacityResult.outcome :=
  capacityResult.verified

theorem aggregate_work :
    aggregateResult.checks <= capability.workCoefficient *
      (capability.inputSize (previous .aggregate) + 1) ^
        capability.workDegree :=
  aggregateResult.checks_le_polynomial

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

abbrev spec := _root_.Hypostructure.Graph.CT14.aggregateSpec objectQuery
  (fun _previous => Fin 3) (fun _previous => Bool)
  (fun previous _object member => Neutral.memberLowerMass previous member)
  (fun previous _object member => Neutral.memberCapacity previous member)
  (fun previous _object member => Neutral.memberLabel previous member)

def capability : _root_.Hypostructure.CT14.Capability spec :=
  _root_.Hypostructure.Graph.CT14.aggregateCapability objectQuery
    (fun _previous => Fin 3) (fun _previous => Bool)
    (fun previous _object member => Neutral.memberLowerMass previous member)
    (fun previous _object member => Neutral.memberCapacity previous member)
    (fun previous _object member => Neutral.memberLabel previous member)
    Neutral.memberQuery (fun _previous => inferInstance)
    (fun _previous => 0) 10 0 (fun previous => by
      change _root_.Hypostructure.CT14.localCheckBound
        (Core.Residual.residualOf previous).members <= 10
      exact (Core.Residual.residualOf previous).work_le_ten)

def result := _root_.Hypostructure.CT14.execute spec capability
  (Neutral.previous .capacity)

theorem terminal : result.terminal = .capacity := by decide

theorem verified : _root_.Hypostructure.CT14.OutcomeClaim result.outcome :=
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

abbrev spec := _root_.Hypostructure.PDE.CT14.aggregateSpec model stateQuery
  (fun _previous => Fin 3) (fun _previous => Bool)
  (fun previous _state member => Neutral.memberLowerMass previous member)
  (fun previous _state member => Neutral.memberCapacity previous member)
  (fun previous _state member => Neutral.memberLabel previous member)

def capability : _root_.Hypostructure.CT14.Capability spec :=
  _root_.Hypostructure.PDE.CT14.aggregateCapability model stateQuery
    (fun _previous => Fin 3) (fun _previous => Bool)
    (fun previous _state member => Neutral.memberLowerMass previous member)
    (fun previous _state member => Neutral.memberCapacity previous member)
    (fun previous _state member => Neutral.memberLabel previous member)
    Neutral.memberQuery (fun _previous => inferInstance)
    (fun _previous => 0) 10 0 (fun previous => by
      change _root_.Hypostructure.CT14.localCheckBound
        (Core.Residual.residualOf previous).members <= 10
      exact (Core.Residual.residualOf previous).work_le_ten)

def result := _root_.Hypostructure.CT14.execute spec capability
  (Neutral.previous .aggregate)

theorem terminal : result.terminal = .aggregate := by decide

theorem verified : _root_.Hypostructure.CT14.OutcomeClaim result.outcome :=
  result.verified

end PDEAdapter

#print axioms Neutral.unbounded_verified
#print axioms Neutral.missingLabel_verified
#print axioms Neutral.aggregate_verified
#print axioms Neutral.capacity_verified
#print axioms GraphAdapter.verified
#print axioms PDEAdapter.verified

end Hypostructure.Fixtures.CT14
