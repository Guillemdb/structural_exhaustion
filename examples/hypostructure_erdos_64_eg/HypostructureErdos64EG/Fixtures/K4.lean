import HypostructureErdos64EG.Node3

namespace HypostructureErdos64EG.Fixtures.K4

open Hypostructure

abbrev Vertex := Fin 4

/-- The complete graph on four explicitly ordered vertices. -/
def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

/-- The literal closed walk `0-1-2-3-0`. -/
def fourCycle : graph.Walk (0 : Vertex) 0 :=
  .cons (v := 1) (by simp [graph])
    (.cons (v := 2) (by simp [graph])
      (.cons (v := 3) (by simp [graph])
        (.cons (v := 0) (by simp [graph]) .nil)))

theorem fourCycle_length : fourCycle.length = 4 :=
  rfl

theorem fourCycle_isCycle : fourCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  decide

theorem four_is_accepted : PowerOfTwoLength 4 := by
  decide

theorem five_is_rejected : ¬PowerOfTwoLength 5 := by
  decide

theorem k4Baseline : Baseline object := by
  change 3 ≤ (⊤ : SimpleGraph Vertex).minDegree
  simp

def k4Certificate : Graph.CycleCertificate object PowerOfTwoLength := by
  dsimp only [object, Graph.FiniteObject.of]
  exact {
    vertex := 0
    walk := fourCycle
    isCycle := fourCycle_isCycle
    length_ok := by
      simpa only [fourCycle_length] using four_is_accepted
  }

theorem k4Target : Target object := by
  exact ⟨k4Certificate⟩

def rootResidual : InitialResidual where
  object := object
  baseline := k4Baseline

def rootStage : InitialStage :=
  initialStage rootResidual

noncomputable def node2Stage : Node2Stage :=
  node2 rootStage

theorem rootStage_exact :
    Core.Residual.residualOf rootStage = rootResidual :=
  rfl

theorem node2Stage_is_noBranch :
    ∃ proof : IsNotCounterexample rootStage,
      node2Stage.added = Core.Residual.Decision.Binary.noBranch proof :=
  node2_no_branch_of_target rootStage k4Target

/-- The framework-generated focus proof for node 2's exact no constructor. -/
noncomputable def node3Active :
    (Core.Residual.Focus.no
      (Yes := IsCounterexample) (No := IsNotCounterexample)).Active node2Stage := by
  rcases node2Stage_is_noBranch with ⟨proof, selected⟩
  exact ⟨proof, selected⟩

/-- Node 3 consumes the focused no branch and returns direct closure. -/
noncomputable def node3Stage :
    Core.Closure.Result (Node3OfficialConclusion node2Stage.previous) :=
  node3 node2Stage node3Active

theorem node3Active_exact_selection :
    node2Stage.added =
      Core.Residual.Decision.Binary.noBranch node3Active.proof :=
  node3Active.selected

theorem k4OfficialConclusion :
    ∃ (exponent : Nat) (vertex : object.Vertex)
      (cycle : object.graph.Walk vertex vertex),
      exponent ≥ 2 ∧ cycle.IsCycle ∧ cycle.length = 2 ^ exponent :=
  (target_iff_official_conclusion object).mp k4Target

#print axioms fourCycle_isCycle
#print axioms five_is_rejected
#print axioms k4Baseline
#print axioms k4Target
#print axioms k4OfficialConclusion
#print axioms node2Stage_is_noBranch
#print axioms node3Stage

end HypostructureErdos64EG.Fixtures.K4
