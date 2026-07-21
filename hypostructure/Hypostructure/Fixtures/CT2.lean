import Hypostructure.Graph.CT2

/-!
# CT2 vertical-slice fixtures

The neutral fixture checks both ways a selected piece can fail eligibility.
The graph fixture checks a residual-selected certified edge and obtains its
deletion criticality without deriving an edge universe in CT2.
-/

namespace Hypostructure.Fixtures.CT2

namespace Neutral

abbrev problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _object => True
  BranchState := fun _object => Unit

def target (object : Nat) : Prop := object = 0

def progress : Core.Progress problem where
  Measure := Nat
  lt := (fun smaller larger => smaller < larger)
  wellFounded := wellFounded_lt
  measure := id

def context : Core.MinimalCounterexampleContext problem target progress where
  toAvoidingContext := {
    toBranchContext := {
      G := 1
      baseline := trivial
      state := ()
    }
    avoids := by simp [target]
  }
  minimal := by
    intro candidate smaller _baseline
    change candidate = 0
    change candidate < 1 at smaller
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ smaller)

structure Residual where
  inheritedContext : Core.MinimalCounterexampleContext problem target progress
  pieces : Core.Finite.Enumeration Unit
  selected : Fin pieces.card

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def contextQuery : Core.Residual.Query Previous fun _previous =>
    Core.MinimalCounterexampleContext problem target progress :=
  residualQuery.map fun previous _residual =>
    (Core.Residual.residualOf previous).inheritedContext

def piecesQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Unit :=
  residualQuery.map fun previous _residual =>
    (Core.Residual.residualOf previous).pieces

def selectedIndexQuery : Core.Residual.Query Previous fun previous =>
    Fin (piecesQuery.read previous).card :=
  residualQuery.map fun previous _residual => by
    let source := Core.Residual.residualOf previous
    exact Fin.cast (by rfl) source.selected

def spec : _root_.Hypostructure.CT2.Spec problem Previous where
  Piece := fun _object => Unit
  Proper := fun _piece => False
  Admissible := fun _state _piece => True
  delete := fun _piece => 0

def capability : _root_.Hypostructure.CT2.Capability target progress spec where
  context := contextQuery
  pieces := piecesQuery
  selectedIndex := selectedIndexQuery
  properDecidable := fun _piece => .isFalse id
  admissibleDecidable := fun _state _piece => .isTrue trivial
  decreases := by
    intro object _state _piece proper _admissible
    exact proper.elim
  preservesBaseline := by
    intro object _state _piece proper _admissible _baseline
    exact proper.elim
  targetMonotone := by
    intro object _state _piece proper _admissible _baseline _reducedTarget
    exact proper.elim

def schedule : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def falseResidual : Residual where
  inheritedContext := context
  pieces := schedule
  selected := ⟨0, by decide⟩

def falsePrevious : Previous :=
  Core.Residual.Ledger.initial falseResidual

def falseResult : _root_.Hypostructure.CT2.ExecutionResult capability :=
  _root_.Hypostructure.CT2.execute capability falsePrevious

theorem false_previous : falseResult.stage.previous = falsePrevious := rfl

theorem false_residual_preserved :
    Core.Residual.residualOf falseResult.stage = falseResidual := rfl

theorem false_selected_mem :
    capability.selectedPiece falsePrevious ∈
      (capability.piecesAt falsePrevious).values :=
  capability.selectedPiece_mem falsePrevious

theorem false_terminal : falseResult.terminal = .criticality :=
  falseResult.terminal_criticality

theorem false_trace :
    falseResult.traceNodes =
      [.entry, .residualSelection, .eligibilityDecision,
        .criticalityTerminal] := by
  rw [falseResult.trace_exact, false_terminal]
  rfl

theorem false_checks : falseResult.checks = 1 :=
  falseResult.checks_eq_one

theorem false_notProper :
    Not (spec.Proper (capability.selectedPiece falsePrevious)) := by
  apply falseResult.notProper_of_admissible
  trivial

/-- The positive semantic trigger has one mandatory framework-owned closure
terminal and trace.  Its verified result is the expected contradiction. -/
def deletionRun (previous : Previous)
    (eligible : capability.Eligible previous) :=
  _root_.Hypostructure.CT2.closeSelected capability previous eligible

theorem deletion_terminal (previous : Previous)
    (eligible : capability.Eligible previous) :
    (deletionRun previous eligible).terminal = .deletionC2 := rfl

theorem deletion_trace (previous : Previous)
    (eligible : capability.Eligible previous) :
    (deletionRun previous eligible).traceNodes =
      [.entry, .residualSelection, .eligibilityDecision,
        .deletionDecision, .deletionC2Terminal] := rfl

theorem deletion_closes (previous : Previous)
    (eligible : capability.Eligible previous) : False :=
  (deletionRun previous eligible).verified

theorem false_work :
    falseResult.checks <= capability.localDeletionBudget.coefficient *
      (capability.localDeletionBudget.size falsePrevious + 1) ^
        capability.localDeletionBudget.degree :=
  falseResult.checks_le_polynomial

end Neutral

namespace EdgeDeletion

abbrev Vertex := Fin 2

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

def dart : object.graph.Dart := by
  dsimp only [object, Graph.FiniteObject.of]
  exact ⟨(0, 1), by simp [graph]⟩

def edge : object.graph.edgeSet :=
  ⟨dart.edge, dart.edge_mem⟩

def baseline (_candidate : Graph.FiniteObject) : Prop := True

def branchState (_candidate : Graph.FiniteObject) := Unit

abbrev problem := Graph.problem baseline branchState

def target (candidate : Graph.FiniteObject) : Prop :=
  candidate.lexicographicSize ≠ object.lexicographicSize

def progress := Graph.lexicographicProgress baseline branchState

def context : Core.MinimalCounterexampleContext problem target progress where
  toAvoidingContext := {
    toBranchContext := {
      G := object
      baseline := trivial
      state := ()
    }
    avoids := fun differs => differs rfl
  }
  minimal := by
    intro candidate smaller _baseline measureEq
    exact (progress.not_smaller_of_measure_eq measureEq) smaller

def admissible (candidate : Graph.FiniteObject)
    (_state : branchState candidate) (selected : candidate.graph.edgeSet) : Prop :=
  baseline (candidate.deleteEdge selected) ∧
    (target (candidate.deleteEdge selected) -> target candidate)

structure Residual where
  inheritedContext : Core.MinimalCounterexampleContext problem target progress
  edges : Core.Finite.Enumeration inheritedContext.G.graph.edgeSet
  selected : Fin edges.card

abbrev Previous := Core.Residual.Ledger Residual

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def contextQuery : Core.Residual.Query Previous fun _previous =>
    Core.MinimalCounterexampleContext problem target progress :=
  residualQuery.map fun previous _residual =>
    (Core.Residual.residualOf previous).inheritedContext

def edgeQuery : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration ((contextQuery.read previous).G.graph.edgeSet) :=
  residualQuery.map fun previous _residual =>
    (Core.Residual.residualOf previous).edges

def selectedIndexQuery : Core.Residual.Query Previous fun previous =>
    Fin (edgeQuery.read previous).card :=
  residualQuery.map fun previous _residual => by
    let source := Core.Residual.residualOf previous
    exact Fin.cast (by rfl) source.selected

def capability := Graph.CT2.edgeDeletionCapability
  baseline branchState target admissible contextQuery edgeQuery
  selectedIndexQuery
  (fun candidate _state selected => by
    dsimp [admissible, baseline, target]
    infer_instance)
  (by
    intro candidate _state selected allowed _baseline
    exact allowed.1)
  (by
    intro candidate _state selected allowed _baseline reducedTarget
    exact allowed.2 reducedTarget)

noncomputable def residual : Residual where
  inheritedContext := context
  edges := {
    values := [by simpa [context] using edge]
    nodup := by simp
    decEq := Classical.decEq _
  }
  selected := ⟨0, by simp [Core.Finite.Enumeration.card]⟩

noncomputable def previous : Previous :=
  Core.Residual.Ledger.initial residual

noncomputable def result :
    _root_.Hypostructure.CT2.ExecutionResult capability :=
  _root_.Hypostructure.CT2.execute capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_residual_preserved :
    Core.Residual.residualOf result.stage = residual := rfl

theorem selected_edge_mem :
    capability.selectedPiece previous ∈
      (capability.piecesAt previous).values :=
  Graph.CT2.selectedEdge_mem previous

theorem result_terminal : result.terminal = .criticality :=
  result.terminal_criticality

theorem result_trace :
    result.traceNodes =
      [.entry, .residualSelection, .eligibilityDecision,
        .criticalityTerminal] := by
  rw [result.trace_exact, result_terminal]
  rfl

theorem result_checks : result.checks = 1 :=
  result.checks_eq_one

theorem selected_edge_notAdmissible :
    Not (admissible
      (capability.contextAt previous).G
      (capability.contextAt previous).state
      (capability.selectedPiece previous)) := by
  simpa [result_previous] using Graph.CT2.selectedEdge_notAdmissible result

theorem deletion_decreases :
    (object.deleteEdge edge).LexicographicallySmaller object :=
  (Graph.ProperSubgraph.deleteEdge object edge).decreases

end EdgeDeletion

#print axioms Neutral.false_terminal
#print axioms Neutral.false_trace
#print axioms Neutral.false_checks
#print axioms Neutral.false_work
#print axioms Neutral.false_residual_preserved
#print axioms Neutral.false_notProper
#print axioms Neutral.deletion_closes
#print axioms EdgeDeletion.result_terminal
#print axioms EdgeDeletion.result_trace
#print axioms EdgeDeletion.result_checks
#print axioms EdgeDeletion.result_residual_preserved
#print axioms EdgeDeletion.selected_edge_notAdmissible
#print axioms EdgeDeletion.deletion_decreases

end Hypostructure.Fixtures.CT2
