import Hypostructure.Graph.CT16
import Hypostructure.PDE.CT16

/-!
# CT16 vertical-slice fixtures

The neutral fixture exercises every terminal on the same residual-owned
coordinate schedule.  The Graph and PDE fixtures verify that both domain
adapters are only semantic instantiations of that executor.
-/

namespace Hypostructure.Fixtures.CT16

namespace Neutral

inductive Mode where
  | proper
  | exact
  | mismatch
  deriving DecidableEq, Repr

def coordinateSchedule : Core.Finite.Enumeration (Fin 3) :=
  Core.Finite.Enumeration.ofNodupList [0, 1, 2] (by decide)

structure Residual where
  mode : Mode
  coordinates : Core.Finite.Enumeration (Fin 3)
  coordinates_eq : coordinates = coordinateSchedule

abbrev Previous := Core.Residual.Ledger Residual

def inSupport : Mode -> Fin 3 -> Prop
  | .proper, coordinate => coordinate ≠ 1
  | .exact, _coordinate => True
  | .mismatch, _coordinate => True

def computedCode : Mode -> Bool
  | .proper => false
  | .exact => false
  | .mismatch => true

def spec : _root_.Hypostructure.CT16.Spec Previous where
  Coordinate := fun _previous => Fin 3
  InSupport := fun previous coordinate =>
    inSupport (Core.Residual.residualOf previous).mode coordinate
  ClosedCode := fun _previous => Bool
  closedCode := fun previous =>
    computedCode (Core.Residual.residualOf previous).mode
  targetCode := fun _previous => false

def coordinateQuery : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Coordinate previous) :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual)).map
      fun _previous residual => residual.coordinates

def capability : _root_.Hypostructure.CT16.Capability spec where
  coordinates := coordinateQuery
  inSupportDecidable := by
    intro previous coordinate
    cases mode : (Core.Residual.residualOf previous).mode <;>
      simp [spec, inSupport, mode] <;> infer_instance
  codeDecidableEq := by
    intro _previous
    change DecidableEq Bool
    infer_instance

def residual (mode : Mode) : Residual where
  mode := mode
  coordinates := coordinateSchedule
  coordinates_eq := rfl

def previous (mode : Mode) : Previous :=
  Core.Residual.Ledger.initial (residual mode)

def properResult : _root_.Hypostructure.CT16.ExecutionResult spec capability :=
  _root_.Hypostructure.CT16.execute spec capability (previous .proper)

def exactResult : _root_.Hypostructure.CT16.ExecutionResult spec capability :=
  _root_.Hypostructure.CT16.execute spec capability (previous .exact)

def mismatchResult : _root_.Hypostructure.CT16.ExecutionResult spec capability :=
  _root_.Hypostructure.CT16.execute spec capability (previous .mismatch)

theorem proper_previous :
    properResult.stage.previous = previous .proper := rfl

theorem exact_previous :
    exactResult.stage.previous = previous .exact := rfl

theorem mismatch_previous :
    mismatchResult.stage.previous = previous .mismatch := rfl

theorem proper_terminal : properResult.terminal = .properSupport := rfl

theorem exact_terminal : exactResult.terminal = .exactCode := rfl

theorem mismatch_terminal : mismatchResult.terminal = .mismatch := rfl

theorem proper_support_checks : properResult.supportChecks = 2 := rfl

theorem exact_support_checks : exactResult.supportChecks = 3 := rfl

theorem mismatch_support_checks : mismatchResult.supportChecks = 3 := rfl

theorem proper_checks : properResult.checks = 2 := rfl

theorem exact_checks : exactResult.checks = 5 := rfl

theorem mismatch_checks : mismatchResult.checks = 5 := rfl

theorem proper_trace :
    properResult.traceNodes =
      [.entry, .coordinateSchedule, .supportScan, .properSupportTerminal] :=
  rfl

theorem exact_trace :
    exactResult.traceNodes =
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .exactCodeTerminal] :=
  rfl

theorem mismatch_trace :
    mismatchResult.traceNodes =
      [.entry, .coordinateSchedule, .supportScan, .closedCodeComputation,
        .codeEqualityDecision, .mismatchTerminal] :=
  rfl

/-- The canonical support scan reports coordinate `1`, after checking `0`. -/
theorem proper_first_missing :
    (_root_.Hypostructure.CT16.supportScan spec capability
      (previous .proper)).index? = some 1 := rfl

theorem proper_missing_absent :
    Not (spec.InSupport (previous .proper) (1 : Fin 3)) := by
  simp [spec, previous, residual, inSupport]

theorem proper_prefix_present :
    spec.InSupport (previous .proper) (0 : Fin 3) := by
  simp [spec, previous, residual, inSupport]

theorem exact_closed_type :
    _root_.Hypostructure.CT16.ExactClosedType spec (previous .exact)
      (capability.coordinatesAt (previous .exact)) :=
  by
    have verified := exactResult.verified
    rw [exact_previous, exact_terminal] at verified
    exact verified

theorem mismatch_closed_type :
    _root_.Hypostructure.CT16.WholeSupport spec (previous .mismatch)
        (capability.coordinatesAt (previous .mismatch)) ∧
      spec.closedCode (previous .mismatch) ≠
        spec.targetCode (previous .mismatch) :=
  by
    have verified := mismatchResult.verified
    rw [mismatch_previous, mismatch_terminal] at verified
    exact verified

theorem proper_work_bound :
    properResult.checks ≤
      capability.worstCaseChecks (previous .proper) :=
  properResult.checks_le_worstCase

theorem exact_work_bound :
    exactResult.checks ≤
      capability.worstCaseChecks (previous .exact) :=
  exactResult.checks_le_worstCase

theorem mismatch_work_bound :
    mismatchResult.checks ≤
      capability.worstCaseChecks (previous .mismatch) :=
  mismatchResult.checks_le_worstCase

end Neutral

namespace GraphVertex

abbrev Vertex := Fin 3

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

structure Residual where
  selected : Graph.FiniteObject

abbrev Previous := Core.Residual.Ledger Residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual)).map
      fun _previous residual => residual.selected

def inSupport (selected : Graph.FiniteObject)
    (_vertex : selected.Vertex) : Prop := True

def spec := Graph.CT16.vertexSpec objectQuery inSupport Nat
  (fun selected => selected.vertices.card) 3

def capability := Graph.CT16.vertexCapability objectQuery inSupport Nat
  (fun selected => selected.vertices.card) 3
  (fun _selected _vertex => .isTrue trivial) inferInstance

def previous : Previous :=
  Core.Residual.Ledger.initial ⟨object⟩

def result : _root_.Hypostructure.CT16.ExecutionResult spec capability :=
  _root_.Hypostructure.CT16.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .exactCode := rfl

theorem result_checks : result.checks = 5 := rfl

theorem result_exact_code :
    _root_.Hypostructure.CT16.ExactClosedType spec previous
      (capability.coordinatesAt previous) :=
  result.verified

end GraphVertex

namespace PDECompactification

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

def coordinateSchedule : Core.Finite.Enumeration (Fin 2) :=
  Core.Finite.Enumeration.ofNodupList [0, 1] (by decide)

structure Residual where
  object : Bool
  coordinates : Core.Finite.Enumeration (Fin 2)

abbrev Previous := Core.Residual.Ledger Residual

def objectQuery : Core.Residual.Query Previous fun _previous =>
    model.problem.Ambient :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual)).map
      fun _previous residual => residual.object

def coordinateQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration (Fin 2) :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual)).map
      fun _previous residual => residual.coordinates

def inSupport (object : Bool) (_coordinate : Fin 2) : Prop := object = true

def spec := PDE.CT16.compactifiedSpec model objectQuery (Fin 2)
  inSupport Bool id true

def capability := PDE.CT16.compactifiedCapability model objectQuery (Fin 2)
  coordinateQuery inSupport Bool id true
  (fun object _coordinate => Bool.decEq object true) inferInstance

def previous : Previous :=
  Core.Residual.Ledger.initial ⟨true, coordinateSchedule⟩

def result : _root_.Hypostructure.CT16.ExecutionResult spec capability :=
  _root_.Hypostructure.CT16.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .exactCode := rfl

theorem result_checks : result.checks = 4 := rfl

theorem result_exact_code :
    _root_.Hypostructure.CT16.ExactClosedType spec previous
      (capability.coordinatesAt previous) :=
  result.verified

end PDECompactification

#print axioms Neutral.proper_previous
#print axioms Neutral.proper_terminal
#print axioms Neutral.proper_checks
#print axioms Neutral.proper_first_missing
#print axioms Neutral.exact_terminal
#print axioms Neutral.exact_checks
#print axioms Neutral.exact_closed_type
#print axioms Neutral.mismatch_terminal
#print axioms Neutral.mismatch_checks
#print axioms Neutral.mismatch_closed_type
#print axioms GraphVertex.result_terminal
#print axioms GraphVertex.result_checks
#print axioms GraphVertex.result_exact_code
#print axioms PDECompactification.result_terminal
#print axioms PDECompactification.result_checks
#print axioms PDECompactification.result_exact_code

end Hypostructure.Fixtures.CT16
