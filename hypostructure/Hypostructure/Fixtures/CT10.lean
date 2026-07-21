import Hypostructure.Graph.CT10
import Hypostructure.PDE.CT10
import Hypostructure.PDE.NavierStokes.Basic

/-!
# CT10 vertical-slice fixtures

The neutral fixtures force all three terminals and pin the declared class
order.  Graph and PDE fixtures then instantiate the two thin semantic adapters
without introducing another finite carrier or any application route.
-/

namespace Hypostructure.Fixtures.CT10

namespace Neutral

abbrev Class := Fin 3

/-- Deliberately nonnumeric class order: `2`, then `0`, then `1`. -/
def orderedClasses : Core.Finite.CompleteEnumeration Class where
  toEnumeration :=
    Core.Finite.Enumeration.ofNodupList [2, 0, 1] (by decide)
  complete := by
    intro cls
    change cls ∈ [2, 0, 1]
    fin_cases cls <;> simp

structure Residual where
  data : Core.Finite.Enumeration Class
  classes : Core.Finite.CompleteEnumeration Class
  directClass : Option Class
  completeWork : classes.toEnumeration.card +
    classes.toEnumeration.card * data.card <= 12

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def dataQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Class :=
  residualQuery.map fun _previous residual => residual.data

def classesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Class :=
  residualQuery.map fun _previous residual => residual.classes

abbrev spec : _root_.Hypostructure.CT10.Spec Previous where
  Datum := fun _previous => Class
  Class := fun _previous => Class
  Promotion := fun _previous => Class
  classOf := fun _previous datum => datum
  Direct := fun previous cls =>
    (Core.Residual.residualOf previous).directClass = some cls
  promote := fun _previous cls => cls

def capability : _root_.Hypostructure.CT10.Capability spec where
  data := dataQuery
  classes := classesQuery
  directDecidable := by
    intro previous cls
    change Decidable
      ((Core.Residual.residualOf previous).directClass = some cls)
    infer_instance
  inputSize := fun _previous => 0
  workCoefficient := 12
  workDegree := 0
  workBound := by
    intro previous
    change (Core.Residual.residualOf previous).classes.toEnumeration.card +
      (Core.Residual.residualOf previous).classes.toEnumeration.card *
        (Core.Residual.residualOf previous).data.card <= 12
    exact
      (Core.Residual.residualOf previous).completeWork

def directInput : Residual where
  data := Core.Finite.Enumeration.singleton 2
  classes := orderedClasses
  directClass := some 1
  completeWork := by decide

def directPrevious : Previous := Core.Residual.Ledger.initial directInput

def directResult :=
  _root_.Hypostructure.CT10.execute capability directPrevious

theorem direct_previous : directResult.stage.previous = directPrevious := rfl

theorem direct_terminal : directResult.terminal = .direct := by decide

theorem direct_checks : directResult.checks = 3 := by decide

theorem direct_trace : directResult.traceNodes =
    [.entry, .classSchedule, .directSearch, .directTerminal] := by decide

def directCertificate := directResult.directResidual direct_terminal

theorem direct_class_order : directCertificate.index.1 = 2 := by decide

theorem direct_class_value : directCertificate.value = (1 : Class) := by decide

def promotedInput : Residual where
  data := Core.Finite.Enumeration.singleton 2
  classes := orderedClasses
  directClass := none
  completeWork := by decide

def promotedPrevious : Previous :=
  Core.Residual.Ledger.initial promotedInput

def promotedResult :=
  _root_.Hypostructure.CT10.execute capability promotedPrevious

theorem promoted_previous :
    promotedResult.stage.previous = promotedPrevious := rfl

theorem promoted_terminal : promotedResult.terminal = .promoted := by decide

theorem promoted_checks : promotedResult.checks = 5 := by decide

theorem promoted_trace : promotedResult.traceNodes =
    [.entry, .classSchedule, .directSearch, .datumSchedule,
      .rowObservation, .firstMissingSearch, .promotion,
      .promotedTerminal] := by decide

def promotedResidual :=
  promotedResult.promotedResidual promoted_terminal

theorem promoted_first_missing_index :
    promotedResidual.missing.index.1 = 1 := by decide

theorem promoted_first_missing_class :
    promotedResidual.missing.value = (0 : Class) := by decide

theorem promoted_payload : promotedResidual.promotion = (0 : Class) := by decide

theorem promoted_earlier_class_observed :
    _root_.Hypostructure.CT10.Observed capability promotedPrevious 2 := by
  apply promotedResidual.earlier_observed
  change (2 : Class) ∈ [2]
  simp

def exhaustiveInput : Residual where
  data := Core.Finite.Enumeration.ofNodupList [2, 0, 1] (by decide)
  classes := orderedClasses
  directClass := none
  completeWork := by decide

def exhaustivePrevious : Previous :=
  Core.Residual.Ledger.initial exhaustiveInput

def exhaustiveResult :=
  _root_.Hypostructure.CT10.execute capability exhaustivePrevious

theorem exhaustive_previous :
    exhaustiveResult.stage.previous = exhaustivePrevious := rfl

theorem exhaustive_terminal :
    exhaustiveResult.terminal = .exhaustive := by decide

theorem exhaustive_checks : exhaustiveResult.checks = 9 := by decide

theorem exhaustive_trace : exhaustiveResult.traceNodes =
    [.entry, .classSchedule, .directSearch, .datumSchedule,
      .rowObservation, .firstMissingSearch, .exhaustiveTerminal] := by decide

def exhaustiveCertificate :=
  exhaustiveResult.exhaustiveCertificate exhaustive_terminal

theorem exhaustive_populated (cls : Class) :
    _root_.Hypostructure.CT10.Observed capability exhaustivePrevious cls :=
  exhaustiveCertificate.populated cls

theorem exhaustive_no_direct (cls : Class) :
    Not (spec.Direct exhaustivePrevious cls) :=
  exhaustiveCertificate.no_direct cls

theorem exhaustive_work :
    exhaustiveResult.checks <= capability.workCoefficient *
      (capability.inputSize exhaustivePrevious + 1) ^ capability.workDegree :=
  exhaustiveResult.checks_le_polynomial

end Neutral

namespace GraphVertex

abbrev Vertex := Fin 3

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of (SimpleGraph.completeGraph Vertex) inferInstance (by
    change DecidableRel fun left right : Vertex => Not (left = right)
    infer_instance)

def boolClasses : Core.Finite.CompleteEnumeration Bool where
  toEnumeration :=
    Core.Finite.Enumeration.ofNodupList [true, false] (by decide)
  complete := by
    intro cls
    change cls ∈ [true, false]
    cases cls <;> simp

structure Residual where
  object : Graph.FiniteObject
  classes : Core.Finite.CompleteEnumeration Bool
  completeWork : classes.toEnumeration.card +
    classes.toEnumeration.card * object.vertices.card <= 8

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  residualQuery.map fun _previous residual => residual.object

def classesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.classes

abbrev spec := Graph.CT10.vertexSpec objectQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _vertex => true)
  (fun _previous _cls => False)
  (fun _previous cls => cls)

def input : Residual where
  object := object
  classes := boolClasses
  completeWork := by decide

def previous : Previous := Core.Residual.Ledger.initial input

def capability := Graph.CT10.vertexCapability objectQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _vertex => true)
  (fun _previous _cls => False)
  (fun _previous cls => cls)
  classesQuery (fun _previous _cls => .isFalse id)
  (fun _previous => 0) 8 0 (by
    intro current
    change (Core.Residual.residualOf current).classes.toEnumeration.card +
      (Core.Residual.residualOf current).classes.toEnumeration.card *
        (Core.Finite.Enumeration.ofFinEnum
          (Core.Residual.residualOf current).object.vertices).card <= 8
    rw [Core.Finite.Enumeration.card_ofFinEnum]
    exact (Core.Residual.residualOf current).completeWork)

def result := _root_.Hypostructure.CT10.execute capability previous

theorem result_terminal : result.terminal = .promoted := by decide

def promoted := result.promotedResidual result_terminal

theorem first_absent_vertex_class :
    promoted.missing.value = false := by
  change (show Bool from promoted.missing.value) = false
  decide

end GraphVertex

namespace PDEObservable

open PDE.NavierStokes

noncomputable section

def observables : PDE.ObservableInterface model where
  Index := Unit
  Value := fun _index => Real
  observe := fun field _index => field.viscosity
  visible := fun _index _window => True
  localObserve := fun _window field _index => field.viscosity
  localReflect := by
    intro field window index visible
    rfl

structure Residual where
  field : Field
  indices : Core.Finite.Enumeration Unit
  classes : Core.Finite.CompleteEnumeration Bool
  completeWork : classes.toEnumeration.card +
    classes.toEnumeration.card * indices.card <= 4

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous => Field :=
  residualQuery.map fun _previous residual => residual.field

def dataQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Unit :=
  residualQuery.map fun _previous residual => residual.indices

def classesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.classes

abbrev spec := PDE.CT10.observableSpec model observables objectQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _index _value => true)
  (fun _previous _cls => False)
  (fun _previous cls => cls)

def input : Residual where
  field := zeroField 1
  indices := Core.Finite.Enumeration.singleton ()
  classes := GraphVertex.boolClasses
  completeWork := by decide

def previous : Previous := Core.Residual.Ledger.initial input

def capability := PDE.CT10.observableCapability model observables objectQuery
  (fun _previous => Bool) (fun _previous => Bool)
  (fun _previous _index _value => true)
  (fun _previous _cls => False)
  (fun _previous cls => cls)
  dataQuery classesQuery (fun _previous _cls => .isFalse id)
  (fun _previous => 0) 4 0 (by
    intro current
    change (Core.Residual.residualOf current).classes.toEnumeration.card +
      (Core.Residual.residualOf current).classes.toEnumeration.card *
        (Core.Residual.residualOf current).indices.card <= 4
    exact (Core.Residual.residualOf current).completeWork)

def result := _root_.Hypostructure.CT10.execute capability previous

theorem result_terminal : result.terminal = .promoted := by decide

def promoted := result.promotedResidual result_terminal

theorem first_absent_signature : promoted.missing.value = false := by
  change (show Bool from promoted.missing.value) = false
  decide

end

end PDEObservable

#print axioms Neutral.direct_terminal
#print axioms Neutral.direct_class_order
#print axioms Neutral.promoted_terminal
#print axioms Neutral.promoted_first_missing_class
#print axioms Neutral.exhaustive_terminal
#print axioms Neutral.exhaustive_populated
#print axioms GraphVertex.result_terminal
#print axioms PDEObservable.result_terminal
#print axioms _root_.Hypostructure.CT10.run_verified
#print axioms _root_.Hypostructure.CT10.run_total

end Hypostructure.Fixtures.CT10
