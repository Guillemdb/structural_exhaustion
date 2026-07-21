import Hypostructure.Graph.Minimality
import HypostructureErdos64EG.Node7

/-!
# Diagram node 8: no proper minimum-degree-three subgraph

The Graph layer applies strict-progress minimality to every certified proper
subgraph on node 7's exact active branch. The application supplies only the
EG baseline, branch-state initializer, and cycle target.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Minimal context lifted through node 7 without copying it. -/
def node4ContextAtNode7Query :
    Core.Residual.Focus.ActiveQuery Node7Focus
      (fun stage active =>
        Node4Output stage.previous.previous.previous.previous active) :=
  node4ContextAtNode6Query.preserve

/-- EG instantiation of Graph's generic cycle-target proper-subgraph profile. -/
def node8MinimalityProfile :
    Graph.ProperSubgraphMinimalityProfile Baseline BranchState Target :=
  Graph.cycleProperSubgraphMinimalityProfile Baseline BranchState
    PowerOfTwoLength (fun _object => ())

/-- Exact accumulated stage emitted by Graph's focused executor. -/
abbrev Node8Stage :=
  Graph.FocusedNoProperBaselineStage Node7Focus node4ContextAtNode7Query

/-- Execute node 8 on the literal node-7 successor. -/
noncomputable def node8 (previous : Node7Stage.{u}) : Node8Stage.{u} :=
  Graph.executeFocusedNoProperBaseline Node7Focus node8MinimalityProfile
    node4ContextAtNode7Query previous

/-- Focus inherited by node 9. -/
abbrev Node8Focus :=
  Graph.FocusedNoProperBaselineProfile Node7Focus node4ContextAtNode7Query

/-- Typed query for Graph's framework-owned no-proper-core certificate. -/
def node8CertificateQuery :=
  Graph.focusedNoProperBaselineQuery Node7Focus node4ContextAtNode7Query

@[simp] theorem node8_previous (previous : Node7Stage.{u}) :
    (node8 previous).previous = previous :=
  rfl

/-- Every certified proper subgraph fails the minimum-degree-three baseline. -/
theorem node8_noProperCore (stage : Node8Stage.{u})
    (active : Node8Focus.Active stage)
    (subgraph : Graph.ProperSubgraph
      (node4ContextAtNode7Query.read stage.previous active).G) :
    Not (Baseline subgraph.value) :=
  (node8CertificateQuery.read stage active).excludes subgraph

/-- Every hypothetical proper core closes by Core's strict-progress mechanism. -/
theorem node8_closure_mechanism (stage : Node8Stage.{u})
    (active : Node8Focus.Active stage)
    (subgraph : Graph.ProperSubgraph
      (node4ContextAtNode7Query.read stage.previous active).G)
    (baseline : Baseline subgraph.value) :
    ((node8CertificateQuery.read stage active).closure subgraph baseline).mechanism =
      Core.Closure.Mechanism.strictProgress :=
  (node8CertificateQuery.read stage active).mechanism subgraph baseline

#print axioms node8
#print axioms node8_noProperCore
#print axioms node8_closure_mechanism

end HypostructureErdos64EG
