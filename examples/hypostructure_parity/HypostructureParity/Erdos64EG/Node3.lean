import Erdos64EG.Node3
import HypostructureErdos64EG.Node3
import HypostructureParity.Erdos64EG.Node2

namespace HypostructureParity.Erdos64EG.Node3

open Hypostructure

universe u

/-!
# Diagram node 3 parity

Node `[3]` is the terminal reached by the negative branch of the node `[2]`
counterexample decision.  The legacy facade is only an import wrapper, so
parity is stated against the legacy internal target/official-conclusion
theorems and the Hypostructure direct Core closure.
-/

/-- The Hypostructure node-3 terminal proposition is equivalent to the
legacy target predicate on the normalized root graph. -/
theorem officialConclusion_iff_legacy_target
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node3OfficialConclusion
        (HypostructureErdos64EG.node1 root) ↔
      _root_.Erdos64EG.Internal.Target
        (Node1.legacyView root.object) := by
  change
    (∃ (exponent : Nat) (vertex : root.object.Vertex)
        (cycle : root.object.graph.Walk vertex vertex),
      exponent ≥ 2 ∧ cycle.IsCycle ∧ cycle.length = 2 ^ exponent) ↔
      _root_.Erdos64EG.Internal.Target
        (Node1.legacyView root.object)
  exact
    (HypostructureErdos64EG.target_iff_official_conclusion
      root.object).symm.trans
      (Node2.target_iff root.object).symm

/-- The new node-3 direct closure proves the same normalized legacy target
as the old terminal branch. -/
theorem node3_closure_proves_legacy_target
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      (Core.Residual.Focus.no
        (Yes := HypostructureErdos64EG.IsCounterexample)
        (No := HypostructureErdos64EG.IsNotCounterexample)).Active
        (HypostructureErdos64EG.node2
          (HypostructureErdos64EG.node1 root))) :
    _root_.Erdos64EG.Internal.Target
      (Node1.legacyView root.object) := by
  have closed :
      HypostructureErdos64EG.Node3OfficialConclusion
        (HypostructureErdos64EG.node1 root) := by
    simpa using
      (HypostructureErdos64EG.node3
        (HypostructureErdos64EG.node2
          (HypostructureErdos64EG.node1 root)) active).proof
  exact (officialConclusion_iff_legacy_target root).mp closed

/-- A legacy-visible target certificate selects the new node-2 negative
branch, so node `[3]` is the matching terminal closure. -/
theorem legacy_target_routes_to_node3
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (target :
      _root_.Erdos64EG.Internal.Target
        (Node1.legacyView root.object)) :
    ∃ _active :
      (Core.Residual.Focus.no
        (Yes := HypostructureErdos64EG.IsCounterexample)
        (No := HypostructureErdos64EG.IsNotCounterexample)).Active
        (HypostructureErdos64EG.node2
          (HypostructureErdos64EG.node1 root)),
      _root_.Erdos64EG.Internal.Target
        (Node1.legacyView root.object) := by
  rcases HypostructureErdos64EG.node2_no_branch_of_target
      (HypostructureErdos64EG.node1 root)
      ((Node2.notCounterexampleTarget_iff root).mp target) with
    ⟨proof, selected⟩
  exact ⟨⟨proof, selected⟩, node3_closure_proves_legacy_target root ⟨proof, selected⟩⟩

#print axioms officialConclusion_iff_legacy_target
#print axioms node3_closure_proves_legacy_target
#print axioms legacy_target_routes_to_node3

end HypostructureParity.Erdos64EG.Node3
