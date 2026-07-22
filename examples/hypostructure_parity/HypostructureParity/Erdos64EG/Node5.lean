import Erdos64EG.Node5
import HypostructureErdos64EG.Node5
import HypostructureParity.Erdos64EG.Node4
import HypostructureParity.Erdos64EG.TargetAlgebra

namespace HypostructureParity.Erdos64EG.Node5

open Hypostructure

universe u

/-!
# Diagram node 5 parity

Node `[5]` consumes the exact node-`[4]` minimal-counterexample branch and
registers the edge-rooted Mersenne-return target algebra.  The parity surface
is normalized to the public target/return equivalence and the graph-owned
avoidance certificate carried by the focused successor stage.
-/

/-- Test-only name for the literal root-to-node-4 prefix used by the parity
module. Production nodes still consume only their literal predecessor stage. -/
private noncomputable abbrev rootNode4Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node4Stage.{u} :=
  HypostructureErdos64EG.node4
    (HypostructureErdos64EG.node2
      (HypostructureErdos64EG.node1 root))

/-- Test-only name for the literal root-to-node-5 prefix used by the parity
module. -/
private noncomputable abbrev rootNode5Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node5Stage.{u} :=
  HypostructureErdos64EG.node5 (rootNode4Stage root)

/-- The Hypostructure node-5 certificate exposes the manuscript-visible
Mersenne-return algebra on the selected node-4 graph. -/
theorem selected_target_algebra_facts
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node5Focus.Active
        (rootNode5Stage root)) :
    let stage := rootNode5Stage root
    let ctx := HypostructureErdos64EG.node4ContextAtNode5Query.read
      stage active
    HypostructureErdos64EG.Target ctx.G ↔
      HypostructureErdos64EG.mersenneReturnAlgebra.HasRootedReturn ctx.G := by
  intro stage ctx
  exact HypostructureErdos64EG.node5_target_iff_rootedReturn
    stage.previous active

/-- The certificate stored by node 5 is the exact graph-owned disjointness
form of avoiding all accepted Mersenne return lengths. -/
theorem selected_return_sets_disjoint
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node5Focus.Active
        (rootNode5Stage root)) :
    let stage := rootNode5Stage root
    let ctx := HypostructureErdos64EG.node4ContextAtNode5Query.read
      stage active
    ∀ dart : ctx.G.graph.Dart,
      Disjoint (Graph.returnLengthSet ctx.G dart)
        {length | HypostructureErdos64EG.MersenneLength length} := by
  intro stage ctx dart
  exact (HypostructureErdos64EG.node5CertificateQuery.read
    stage active).returnLengthSetsDisjoint dart

/-- A legacy-visible counterexample reaches the same paper branch through
nodes 2, 4, and 5, and node 5 exposes the public target/return algebra there. -/
theorem legacy_counterexample_routes_to_node5
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (counterexample :
      _root_.Erdos64EG.Internal.IsCounterexample
        (Node1.legacyView root.object)) :
    ∃ active :
      HypostructureErdos64EG.Node5Focus.Active
        (rootNode5Stage root),
      let stage := rootNode5Stage root
      let ctx := HypostructureErdos64EG.node4ContextAtNode5Query.read
        stage active
      (HypostructureErdos64EG.Target ctx.G ↔
        HypostructureErdos64EG.mersenneReturnAlgebra.HasRootedReturn ctx.G) ∧
        ∀ dart : ctx.G.graph.Dart,
          Disjoint (Graph.returnLengthSet ctx.G dart)
            {length | HypostructureErdos64EG.MersenneLength length} := by
  rcases Node4.legacy_counterexample_routes_to_node4 root counterexample with
    ⟨parentActive, _parentFacts⟩
  let previous := rootNode4Stage root
  have active :
      HypostructureErdos64EG.Node5Focus.Active
        (HypostructureErdos64EG.node5 previous) := by
    change
      HypostructureErdos64EG.Node4Focus.Active
        (HypostructureErdos64EG.node5 previous).previous
    simpa [HypostructureErdos64EG.node5_previous] using parentActive
  exact ⟨active,
    selected_target_algebra_facts root active,
    selected_return_sets_disjoint root active⟩

/-- Node 5 parity preserves the same one-check focused-successor budget
exposed by the production node. -/
theorem node5_checks_eq_one
    (previous : HypostructureErdos64EG.Node4Stage.{u}) :
    (HypostructureErdos64EG.node5Counted previous).checks = 1 :=
  HypostructureErdos64EG.node5Counted_checks_eq_one previous

#print axioms selected_target_algebra_facts
#print axioms selected_return_sets_disjoint
#print axioms legacy_counterexample_routes_to_node5
#print axioms node5_checks_eq_one

end HypostructureParity.Erdos64EG.Node5
