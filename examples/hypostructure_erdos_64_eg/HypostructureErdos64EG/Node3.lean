import HypostructureErdos64EG.Node2

/-!
# Diagram node 3: negative counterexample branch

Node 3 closes only node 2's negative branch.  The positive counterexample
branch remains literally present in the predecessor decision stage.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The official conclusion for the exact packed object in a node-1 stage. -/
def Node3OfficialConclusion (stage : Node1Stage.{u}) : Prop :=
  let object := (node1ResidualQuery.read stage).object
  ∃ (exponent : Nat) (vertex : object.Vertex)
      (cycle : object.graph.Walk vertex vertex),
    exponent ≥ 2 ∧ cycle.IsCycle ∧ cycle.length = 2 ^ exponent

/-- Node 3 contributes only the official conclusion on the no branch. -/
abbrev Node3Output (stage : Node1Stage.{u})
    (_target : IsNotCounterexample stage) : Prop :=
  Node3OfficialConclusion stage

/-- Exact accumulated stage after advancing only node 2's no branch. -/
abbrev Node3Stage :=
  Core.Residual.Decision.NoContinuationStage
    (Yes := IsCounterexample) (No := IsNotCounterexample) Node3Output

/-- Execute node 3 through Core's branch continuation machinery. -/
noncomputable def node3 (previous : Node2Stage.{u}) : Node3Stage.{u} :=
  Core.Residual.Decision.continueNo previous fun targetProof =>
    target_iff_official_conclusion
      (node1ResidualQuery.read previous.previous).object |>.mp targetProof

@[simp] theorem node3_previous (previous : Node2Stage.{u}) :
    (node3 previous).previous = previous :=
  rfl

end HypostructureErdos64EG
