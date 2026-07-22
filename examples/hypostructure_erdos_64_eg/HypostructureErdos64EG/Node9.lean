import Hypostructure.Graph.DeletionCriticality
import HypostructureErdos64EG.Node8

/-!
# Diagram node 9: edge-deletion criticality

The Graph layer consumes node 8's minimal context and no-proper-core
certificate through typed ledger queries.  The EG application supplies only
the official minimum-degree threshold.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Minimal context inherited through node 8 by a framework query. -/
def node4ContextAtNode8Query :
    Core.Residual.Focus.ActiveQuery Node8Focus
      (fun stage active =>
        Node4Output stage.previous.previous.previous.previous.previous active) :=
  node4ContextAtNode6AvoidingQuery.preserve

/-- Exact accumulated stage emitted by Graph's deletion-criticality executor. -/
abbrev Node9Stage :=
  Graph.FocusedMinimumDegreeDeletionCriticalityStage 3 Node8Focus
    node4ContextAtNode8Query

/-- Counted node-9 execution from the literal node-8 predecessor. -/
noncomputable def node9Counted (previous : Node8Stage.{u}) :
    Core.Counted Node9Stage.{u} :=
  Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted 3 Node8Focus
    node4ContextAtNode8Query node8CertificateQuery previous

/-- Execute node 9 from the literal node-8 predecessor. -/
noncomputable def node9 (previous : Node8Stage.{u}) : Node9Stage.{u} :=
  (node9Counted previous).value

/-- Focus inherited by node 10. -/
abbrev Node9Focus :=
  Graph.FocusedMinimumDegreeDeletionCriticalityProfile 3 Node8Focus
    node4ContextAtNode8Query

/-- Query Graph's generated endpoint-criticality certificate. -/
def node9CertificateQuery :=
  Graph.focusedMinimumDegreeDeletionCriticalityQuery 3 Node8Focus
    node4ContextAtNode8Query

@[simp] theorem node9_previous (previous : Node8Stage.{u}) :
    (node9 previous).previous = previous :=
  rfl

/-- Every edge has a degree-three endpoint. -/
theorem node9_edge_touches_degree_three (stage : Node9Stage.{u})
    (active : Node9Focus.Active stage)
    (dart : (node4ContextAtNode8Query.read stage.previous active).G.graph.Dart) :
    (node4ContextAtNode8Query.read stage.previous active).G.degree dart.fst = 3 ∨
      (node4ContextAtNode8Query.read stage.previous active).G.degree dart.snd = 3 :=
  (node9CertificateQuery.read stage active).tightEndpoint dart

theorem node9Counted_work_bounded (previous : Node8Stage.{u}) :
    (node9Counted previous).checks <=
      Node8Focus.selectionBudget.coefficient *
        (Node8Focus.selectionBudget.size previous + 1) ^
          Node8Focus.selectionBudget.degree := by
  rw [node9Counted,
    Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted,
    Graph.executeFocusedDeletionCriticalityCounted_checks]
  exact Node8Focus.selectionBudget.bounded previous

#print axioms node9
#print axioms node9Counted_work_bounded
#print axioms node9_edge_touches_degree_three

end HypostructureErdos64EG
