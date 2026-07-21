import Hypostructure.Graph.CT8
import Hypostructure.PDE.CT8

/-!
# CT8 vertical-slice fixtures

The three fixtures cover every terminal.  They pin lexicographic pair order,
first response separation, exact work, one-step ledger retention, and the two
domain adapters.  All finite families are fields of the root residual.
-/

namespace Hypostructure.Fixtures.CT8

def boolUniverse : Core.Finite.CompleteEnumeration Bool where
  toEnumeration := {
    values := [false, true]
    nodup := by simp
    decEq := inferInstance
  }
  complete := by
    intro value
    cases value <;> simp

def finThreeUniverse : Core.Finite.CompleteEnumeration (Fin 3) where
  toEnumeration := {
    values := [0, 1, 2]
    nodup := by simp
    decEq := inferInstance
  }
  complete := by
    intro value
    fin_cases value <;> simp

namespace NeutralNoRepetition

structure Residual where
  states : List (Fin 3)
  exactTypes : Core.Finite.CompleteEnumeration (Fin 3)
  contexts : Core.Finite.CompleteEnumeration Bool
  completeWork : _root_.Hypostructure.CT8.localCheckBound states
    contexts.toEnumeration <= 5

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def sequenceQuery : Core.Residual.Query Previous fun _previous => List (Fin 3) :=
  residualQuery.map fun _previous residual => residual.states

def exactTypeQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration (Fin 3) :=
  residualQuery.map fun _previous residual => residual.exactTypes

def contextQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.contexts

abbrev spec : _root_.Hypostructure.CT8.Spec Previous where
  State := fun _previous => Fin 3
  ExactType := fun _previous => Fin 3
  ResponseContext := fun _previous => Bool
  ResponseValue := fun _previous => Bool
  Removal := fun _previous => Nat
  exactType := fun _previous state => state
  response := fun _previous state _context => state = 0
  StrictlySmaller := fun _previous replacement => replacement < 3

def capability : _root_.Hypostructure.CT8.Capability spec where
  sequence := sequenceQuery
  exactTypes := exactTypeQuery
  responseContexts := contextQuery
  responseValueDecEq := fun _previous => inferInstance
  remove := fun _previous _first _second _sameType _equalResponses => 2
  removeStrict := by
    intro previous first second sameType equalResponses
    change (2 : Nat) < 3
    decide
  inputSize := fun _previous => 0
  workCoefficient := 5
  workDegree := 0
  workBound := by
    intro previous
    change _root_.Hypostructure.CT8.localCheckBound
      (Core.Residual.residualOf previous).states
      (Core.Residual.residualOf previous).contexts.toEnumeration <= 5
    exact (Core.Residual.residualOf previous).completeWork

def residual : Residual where
  states := [0, 1, 2]
  exactTypes := finThreeUniverse
  contexts := boolUniverse
  completeWork := by decide

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT8.ExecutionResult spec capability :=
  _root_.Hypostructure.CT8.execute capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem retains_residual : Core.Residual.residualOf result.stage = residual := rfl

theorem terminal : result.terminal = .noRepetition := by decide

theorem exact_checks : result.checks = 3 := by decide

theorem exact_trace : result.traceNodes =
    [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
      .noRepetitionTerminal] := by decide

def certificate := result.noRepetitionCertificate terminal

def zeroTwo : _root_.Hypostructure.CT8.OrderedIndexPair 3 :=
  ⟨(0, 2), by decide⟩

theorem zero_two_types_differ :
    Not (_root_.Hypostructure.CT8.SameExactType capability previous zeroTwo) :=
  certificate.typesDifferent zeroTwo

theorem semantic_sound :
    _root_.Hypostructure.CT8.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end NeutralNoRepetition

namespace GraphSeparation

abbrev LargeVertex := Fin 2
abbrev SmallVertex := Fin 1

def largeObject : Graph.FiniteObject :=
  Graph.FiniteObject.of (SimpleGraph.completeGraph LargeVertex) inferInstance (by
    change DecidableRel fun left right : LargeVertex => left ≠ right
    infer_instance)

def smallObject : Graph.FiniteObject :=
  Graph.FiniteObject.of (SimpleGraph.completeGraph SmallVertex) inferInstance (by
    change DecidableRel fun left right : SmallVertex => left ≠ right
    infer_instance)

def Baseline (_object : Graph.FiniteObject) : Prop := True

def BranchState (_object : Graph.FiniteObject) := Unit

abbrev problem := Graph.problem Baseline BranchState

def progress := Graph.lexicographicProgress Baseline BranchState

theorem small_strict : progress.Smaller smallObject largeObject :=
  Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by decide)

structure Residual where
  object : Graph.FiniteObject
  candidate : Graph.FiniteObject
  candidateSmaller : progress.Smaller candidate object
  states : List (Fin 3)
  exactTypes : Core.Finite.CompleteEnumeration Bool
  contexts : Core.Finite.CompleteEnumeration Bool
  completeWork : _root_.Hypostructure.CT8.localCheckBound states
    contexts.toEnumeration <= 5

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  residualQuery.map fun _previous residual => residual.object

def sequenceQuery : Core.Residual.Query Previous fun _previous => List (Fin 3) :=
  residualQuery.map fun _previous residual => residual.states

def exactTypeQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.exactTypes

def contextQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.contexts

abbrev State (_previous : Previous) := Fin 3
abbrev ExactType (_previous : Previous) := Bool
abbrev ResponseContext (_previous : Previous) := Bool
abbrev ResponseValue (_previous : Previous) := Bool

def exactType (_previous : Previous) (state : Fin 3) : Bool :=
  state ≠ 0

def response (_previous : Previous) (state : Fin 3)
    (context : Bool) : Bool :=
  context && state = 2

abbrev spec := Graph.CT8.orderedRecurrenceSpec Baseline BranchState progress
  objectQuery State ExactType ResponseContext ResponseValue exactType response

def capability := Graph.CT8.orderedRecurrenceCapability Baseline BranchState
  progress objectQuery State ExactType ResponseContext ResponseValue exactType
  response sequenceQuery exactTypeQuery contextQuery
  (fun _previous => inferInstance)
  (fun previous _first _second _sameType _equalResponses =>
    (Core.Residual.residualOf previous).candidate)
  (by
    intro previous first second sameType equalResponses
    exact (Core.Residual.residualOf previous).candidateSmaller)
  (fun _previous => 0) 5 0 (by
    intro previous
    change _root_.Hypostructure.CT8.localCheckBound
      (Core.Residual.residualOf previous).states
      (Core.Residual.residualOf previous).contexts.toEnumeration <= 5
    exact (Core.Residual.residualOf previous).completeWork)

def residual : Residual where
  object := largeObject
  candidate := smallObject
  candidateSmaller := small_strict
  states := [0, 1, 2]
  exactTypes := boolUniverse
  contexts := boolUniverse
  completeWork := by decide

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT8.ExecutionResult spec capability :=
  _root_.Hypostructure.CT8.execute capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem terminal : result.terminal = .separation := by decide

theorem exact_checks : result.checks = 5 := by decide

theorem exact_trace : result.traceNodes =
    [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
      .responseContextSchedule, .responseSearch, .separationTerminal] := by
  decide

def separated := result.separationResidual terminal

theorem first_repeated_pair_index : separated.pair.index.1 = 2 := by decide

theorem first_repeated_states :
    separated.pair.first = (1 : Fin 3) ∧
      separated.pair.second = (2 : Fin 3) := by
  change (show Fin 3 from separated.pair.first) = 1 ∧
    (show Fin 3 from separated.pair.second) = 2
  decide

theorem first_separator_index : separated.separator.index.1 = 1 := by decide

theorem first_separator_context : separated.separator.context = true := by
  change (show Bool from separated.separator.context) = true
  decide

theorem separator_is_sound :
    _root_.Hypostructure.CT8.ResponseDiffers capability previous
      separated.pair separated.separator.context :=
  separated.separator.differs

end GraphSeparation

namespace PDERemoval

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

def progress : Core.Progress problem where
  Measure := Nat
  lt := (· < ·)
  wellFounded := wellFounded_lt
  measure := id

structure Residual where
  source : Nat
  candidate : Nat
  candidateSmaller : progress.Smaller candidate source
  states : List (Fin 3)
  exactTypes : Core.Finite.CompleteEnumeration Bool
  contexts : Core.Finite.CompleteEnumeration Bool
  completeWork : _root_.Hypostructure.CT8.localCheckBound states
    contexts.toEnumeration <= 5

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def sourceQuery : Core.Residual.Query Previous fun _previous =>
    model.problem.Ambient :=
  residualQuery.map fun _previous residual => residual.source

def sequenceQuery : Core.Residual.Query Previous fun _previous => List (Fin 3) :=
  residualQuery.map fun _previous residual => residual.states

def exactTypeQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.exactTypes

def contextQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.CompleteEnumeration Bool :=
  residualQuery.map fun _previous residual => residual.contexts

abbrev State (_previous : Previous) := Fin 3
abbrev ExactType (_previous : Previous) := Bool
abbrev ResponseContext (_previous : Previous) := Bool
abbrev ResponseValue (_previous : Previous) := Bool

def exactType (_previous : Previous) (state : Fin 3) : Bool :=
  state ≠ 0

def response (_previous : Previous) (_state : Fin 3)
    (_context : Bool) : Bool :=
  false

abbrev spec := PDE.CT8.profileRecurrenceSpec model progress sourceQuery State
  ExactType ResponseContext ResponseValue exactType response

def capability := PDE.CT8.profileRecurrenceCapability model progress
  sourceQuery State ExactType ResponseContext ResponseValue exactType response
  sequenceQuery exactTypeQuery contextQuery (fun _previous => inferInstance)
  (fun previous _first _second _sameType _equalResponses =>
    (Core.Residual.residualOf previous).candidate)
  (by
    intro previous first second sameType equalResponses
    exact (Core.Residual.residualOf previous).candidateSmaller)
  (fun _previous => 0) 5 0 (by
    intro previous
    change _root_.Hypostructure.CT8.localCheckBound
      (Core.Residual.residualOf previous).states
      (Core.Residual.residualOf previous).contexts.toEnumeration <= 5
    exact (Core.Residual.residualOf previous).completeWork)

def residual : Residual where
  source := 3
  candidate := 2
  candidateSmaller := by
    change (2 : Nat) < 3
    decide
  states := [0, 1, 2]
  exactTypes := boolUniverse
  contexts := boolUniverse
  completeWork := by decide

def previous : Previous := Core.Residual.Ledger.initial residual

def result : _root_.Hypostructure.CT8.ExecutionResult spec capability :=
  _root_.Hypostructure.CT8.execute capability previous

theorem retains_predecessor : result.stage.previous = previous := rfl

theorem terminal : result.terminal = .removal := by decide

theorem exact_checks : result.checks = 5 := by decide

theorem exact_trace : result.traceNodes =
    [.entry, .stateSequence, .orderedPairSchedule, .repeatedTypeSearch,
      .responseContextSchedule, .responseSearch, .removalComputation,
      .removalTerminal] := by decide

def certificate := result.removalCertificate terminal

theorem first_repeated_pair_index : certificate.pair.index.1 = 2 := by decide

theorem replacement_exact :
    (show Nat from certificate.replacement) = 2 := by
  decide

theorem replacement_strict :
    progress.Smaller certificate.replacement residual.source :=
  certificate.smaller

theorem responses_equal (context : Bool) :
    response previous certificate.pair.first context =
      response previous certificate.pair.second context :=
  certificate.responsesEqual context

theorem semantic_sound :
    _root_.Hypostructure.CT8.OutcomeClaim result.outcome :=
  result.verified

theorem polynomial_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end PDERemoval

#print axioms NeutralNoRepetition.retains_predecessor
#print axioms NeutralNoRepetition.retains_residual
#print axioms NeutralNoRepetition.terminal
#print axioms NeutralNoRepetition.exact_checks
#print axioms NeutralNoRepetition.exact_trace
#print axioms NeutralNoRepetition.zero_two_types_differ
#print axioms NeutralNoRepetition.semantic_sound
#print axioms NeutralNoRepetition.polynomial_work
#print axioms GraphSeparation.terminal
#print axioms GraphSeparation.exact_checks
#print axioms GraphSeparation.first_repeated_pair_index
#print axioms GraphSeparation.first_separator_context
#print axioms GraphSeparation.separator_is_sound
#print axioms PDERemoval.terminal
#print axioms PDERemoval.exact_checks
#print axioms PDERemoval.replacement_exact
#print axioms PDERemoval.replacement_strict
#print axioms PDERemoval.responses_equal
#print axioms PDERemoval.semantic_sound
#print axioms PDERemoval.polynomial_work
#print axioms _root_.Hypostructure.CT8.run_verified
#print axioms _root_.Hypostructure.CT8.run_total

end Hypostructure.Fixtures.CT8
