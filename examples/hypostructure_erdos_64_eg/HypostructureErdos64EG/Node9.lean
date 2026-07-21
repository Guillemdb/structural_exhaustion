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
  node4ContextAtNode7Query.preserve

/-- Exact accumulated stage emitted by Graph's deletion-criticality executor. -/
abbrev Node9Stage :=
  Graph.FocusedMinimumDegreeDeletionCriticalityStage 3 Node8Focus
    node4ContextAtNode8Query

/-- Execute node 9 from the literal node-8 predecessor. -/
noncomputable def node9 (previous : Node8Stage.{u}) : Node9Stage.{u} :=
  Graph.executeFocusedMinimumDegreeDeletionCriticality 3 Node8Focus
    node4ContextAtNode8Query node8CertificateQuery previous

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

#print axioms node9
#print axioms node9_edge_touches_degree_three

end HypostructureErdos64EG
