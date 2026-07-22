import HypostructureErdos64EG.Node9

/-!
# Diagram node 10: high-degree vertices are independent

Graph derives and registers this consequence of node 9's deletion-criticality
certificate.  No edge argument or proof payload is authored by the EG layer.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Minimal context inherited through node 9 by a framework query. -/
def node4ContextAtNode9Query :
    Core.Residual.Focus.ActiveQuery Node9Focus
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode8Query.preserve

/-- Exact accumulated stage emitted by Graph's independence executor. -/
abbrev Node10Stage :=
  Graph.FocusedSlackVertexIndependenceStage Node9Focus
    (Graph.minimumDegreeDeletionCriticalityProfile 3)
    node4ContextAtNode9Query

/-- Counted node-10 execution from the literal node-9 predecessor. -/
noncomputable def node10Counted (previous : Node9Stage.{u}) :
    Core.Counted Node10Stage.{u} :=
  Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted 3 Node9Focus
    node4ContextAtNode9Query node9CertificateQuery previous

/-- Execute node 10 from the literal node-9 predecessor. -/
noncomputable def node10 (previous : Node9Stage.{u}) : Node10Stage.{u} :=
  (node10Counted previous).value

/-- Focus inherited by node 11. -/
abbrev Node10Focus :=
  Graph.FocusedSlackVertexIndependenceProfile Node9Focus
    (Graph.minimumDegreeDeletionCriticalityProfile 3)
    node4ContextAtNode9Query

/-- Query Graph's registered independence fact. -/
def node10IndependenceQuery :=
  Graph.focusedMinimumDegreeSlackVertexIndependenceQuery 3 Node9Focus
    node4ContextAtNode9Query

@[simp] theorem node10_previous (previous : Node9Stage.{u}) :
    (node10 previous).previous = previous :=
  rfl

/-- Vertices of degree at least four form an independent set. -/
theorem node10_high_degree_vertices_independent (stage : Node10Stage.{u})
    (active : Node10Focus.Active stage)
    {left right : (node4ContextAtNode9Query.read stage.previous active).G.Vertex}
    (leftHigh :
      4 ≤ (node4ContextAtNode9Query.read stage.previous active).G.degree left)
    (rightHigh :
      4 ≤ (node4ContextAtNode9Query.read stage.previous active).G.degree right) :
    Not ((node4ContextAtNode9Query.read stage.previous active).G.graph.Adj
      left right) :=
  node10IndependenceQuery.read stage active leftHigh rightHigh

theorem node10Counted_work_bounded (previous : Node9Stage.{u}) :
    (node10Counted previous).checks <=
      Node9Focus.selectionBudget.coefficient *
        (Node9Focus.selectionBudget.size previous + 1) ^
          Node9Focus.selectionBudget.degree := by
  rw [node10Counted,
    Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted,
    Graph.executeFocusedSlackVertexIndependenceCounted_checks]
  exact Node9Focus.selectionBudget.bounded previous

#print axioms node10
#print axioms node10Counted_work_bounded
#print axioms node10_high_degree_vertices_independent

end HypostructureErdos64EG
