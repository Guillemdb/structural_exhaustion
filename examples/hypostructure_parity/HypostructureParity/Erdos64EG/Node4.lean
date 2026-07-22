import Erdos64EG.Node4
import HypostructureErdos64EG.Node4
import HypostructureParity.Erdos64EG.Node2

namespace HypostructureParity.Erdos64EG.Node4

open Hypostructure

universe u

/-!
# Diagram node 4 parity

Node `[4]` continues only the positive branch of the node `[2]`
counterexample decision and selects a lexicographically minimal
counterexample.  The parity surface is normalized to the branch route and the
public facts carried by the selected minimal context.
-/

/-- The selected Hypostructure node-4 context carries exactly the public
counterexample facts needed downstream: baseline, target avoidance, and the
registered lexicographic minimality kernel. -/
theorem selected_context_facts
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node4Focus.Active
        (HypostructureErdos64EG.node4
          (HypostructureErdos64EG.node2
            (HypostructureErdos64EG.node1 root)))) :
    let ctx := HypostructureErdos64EG.node4ContextQuery.read
      (HypostructureErdos64EG.node4
        (HypostructureErdos64EG.node2
          (HypostructureErdos64EG.node1 root))) active
    HypostructureErdos64EG.problem.Baseline ctx.G ∧
      ¬ HypostructureErdos64EG.Target ctx.G ∧
      Core.MinimalityKernel HypostructureErdos64EG.problem
        HypostructureErdos64EG.Target HypostructureErdos64EG.EGProgress
        ctx.toBranchContext := by
  intro ctx
  exact ⟨ctx.baseline, ctx.avoids, ctx.minimal⟩

/-- A legacy-visible counterexample certificate selects the same positive
paper branch in the Hypostructure node-2 decision and therefore reaches the
node-4 minimal-counterexample context. -/
theorem legacy_counterexample_routes_to_node4
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (counterexample :
      _root_.Erdos64EG.Internal.IsCounterexample
        (Node1.legacyView root.object)) :
    ∃ active :
      HypostructureErdos64EG.Node4Focus.Active
        (HypostructureErdos64EG.node4
          (HypostructureErdos64EG.node2
            (HypostructureErdos64EG.node1 root))),
      let ctx := HypostructureErdos64EG.node4ContextQuery.read
        (HypostructureErdos64EG.node4
          (HypostructureErdos64EG.node2
            (HypostructureErdos64EG.node1 root))) active
      HypostructureErdos64EG.problem.Baseline ctx.G ∧
        ¬ HypostructureErdos64EG.Target ctx.G ∧
        Core.MinimalityKernel HypostructureErdos64EG.problem
          HypostructureErdos64EG.Target HypostructureErdos64EG.EGProgress
          ctx.toBranchContext := by
  let previous :=
    HypostructureErdos64EG.node2
      (HypostructureErdos64EG.node1 root)
  rcases HypostructureErdos64EG.node2_yes_branch_of_counterexample
      (HypostructureErdos64EG.node1 root)
      ((Node2.counterexample_iff root).mp counterexample) with
    ⟨proof, selected⟩
  let parentActive :
      HypostructureErdos64EG.CounterexampleFocus.Active previous :=
    ⟨proof, selected⟩
  have active :
      HypostructureErdos64EG.Node4Focus.Active
        (HypostructureErdos64EG.node4 previous) := by
    change
      HypostructureErdos64EG.CounterexampleFocus.Active
        (HypostructureErdos64EG.node4 previous).previous
    simpa [HypostructureErdos64EG.node4_previous] using parentActive
  exact ⟨active, selected_context_facts root active⟩

/-- Node 4 parity preserves the same one-check focused-branch selection
budget exposed by the production node. -/
theorem node4_checks_eq_one
    (previous : HypostructureErdos64EG.Node2Stage.{u}) :
    (HypostructureErdos64EG.node4Counted previous).checks = 1 :=
  HypostructureErdos64EG.node4Counted_checks_eq_one previous

#print axioms selected_context_facts
#print axioms legacy_counterexample_routes_to_node4
#print axioms node4_checks_eq_one

end HypostructureParity.Erdos64EG.Node4
