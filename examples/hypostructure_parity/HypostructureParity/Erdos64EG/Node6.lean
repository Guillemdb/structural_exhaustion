import Erdos64EG.Node6
import HypostructureErdos64EG.Node6
import HypostructureParity.Erdos64EG.Node5

namespace HypostructureParity.Erdos64EG.Node6

open Hypostructure

universe u

/-!
# Diagram node 6 parity

Node `[6]` consumes the exact node-`[5]` residual and runs the focused
proof-carrying CT1 rooted-return decision.  The normalized parity surface is
the CT1 branch semantics, trace, work, and the framework-owned continuation
from the impossible C1 branch to the avoiding residual consumed by node `[8]`.
-/

private noncomputable abbrev rootNode4Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node4Stage.{u} :=
  HypostructureErdos64EG.node4
    (HypostructureErdos64EG.node2
      (HypostructureErdos64EG.node1 root))

private noncomputable abbrev rootNode5Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node5Stage.{u} :=
  HypostructureErdos64EG.node5 (rootNode4Stage root)

private noncomputable abbrev rootNode6Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node6Stage.{u} :=
  HypostructureErdos64EG.node6 (rootNode5Stage root)

/-- Node 6 exposes CT1's exact terminal-indexed target semantics. -/
theorem selected_ct1_semantics
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node6Focus.Active
        (rootNode6Stage root)) :
    match
      (HypostructureErdos64EG.node6RouteQuery.read
        (rootNode6Stage root) active).terminal
    with
    | .c1 =>
        HypostructureErdos64EG.Target
          (HypostructureErdos64EG.node6ObjectQuery.read
            (rootNode5Stage root) active)
    | .avoiding =>
        Not (HypostructureErdos64EG.Target
          (HypostructureErdos64EG.node6ObjectQuery.read
            (rootNode5Stage root) active)) :=
  HypostructureErdos64EG.node6_semantics (rootNode6Stage root) active

/-- Node 6 preserves CT1's exact public trace for either terminal. -/
theorem selected_ct1_trace_exact
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node6Focus.Active
        (rootNode6Stage root)) :
    (CT1.CertificateEncoding.traceOfRoute
      (HypostructureErdos64EG.node6RouteQuery.read
        (rootNode6Stage root) active)).nodes =
      CT1.CertificateEncoding.TypedTrace.expectedNodes
        (HypostructureErdos64EG.node6RouteQuery.read
          (rootNode6Stage root) active).terminal :=
  HypostructureErdos64EG.node6_trace_exact (rootNode6Stage root) active

/-- The node-5 avoidance certificate makes the CT1 C1 terminal impossible,
so the framework continuation exposes the avoiding residual. -/
theorem selected_continue_avoids
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node6AvoidingFocus.Active
        (HypostructureErdos64EG.node6ContinueAvoiding
          (rootNode6Stage root))) :
    Not (HypostructureErdos64EG.Target
      (HypostructureErdos64EG.node6ObjectQuery.read
        (rootNode5Stage root) active)) :=
  HypostructureErdos64EG.node6_avoids
    (HypostructureErdos64EG.node6ContinueAvoiding
      (rootNode6Stage root)) active

/-- A legacy-visible counterexample reaches the new node-6 CT1 decision
through the same paper branch and exposes the public CT1 semantics. -/
theorem legacy_counterexample_routes_to_node6
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (counterexample :
      _root_.Erdos64EG.Internal.IsCounterexample
        (Node1.legacyView root.object)) :
    ∃ active :
      HypostructureErdos64EG.Node6Focus.Active
        (rootNode6Stage root),
      match
        (HypostructureErdos64EG.node6RouteQuery.read
          (rootNode6Stage root) active).terminal
      with
      | .c1 =>
          HypostructureErdos64EG.Target
            (HypostructureErdos64EG.node6ObjectQuery.read
              (rootNode5Stage root) active)
      | .avoiding =>
          Not (HypostructureErdos64EG.Target
            (HypostructureErdos64EG.node6ObjectQuery.read
              (rootNode5Stage root) active)) := by
  rcases Node5.legacy_counterexample_routes_to_node5 root counterexample with
    ⟨parentActive, _parentFacts⟩
  let previous := rootNode5Stage root
  have active :
      HypostructureErdos64EG.Node6Focus.Active
        (HypostructureErdos64EG.node6 previous) := by
    change
      HypostructureErdos64EG.Node5Focus.Active
        (HypostructureErdos64EG.node6 previous).previous
    simpa [HypostructureErdos64EG.node6_previous] using parentActive
  exact ⟨active, selected_ct1_semantics root active⟩

/-- Node 6 parity preserves the production CT1 work bound. -/
theorem node6_work_bounded
    (previous : HypostructureErdos64EG.Node5Stage.{u}) :
    (HypostructureErdos64EG.node6Counted previous).checks <=
      HypostructureErdos64EG.node6Encoding.workBudget.coefficient *
        (HypostructureErdos64EG.node6Encoding.workBudget.size previous + 1) ^
          HypostructureErdos64EG.node6Encoding.workBudget.degree :=
  HypostructureErdos64EG.node6Counted_work_bounded previous

#print axioms selected_ct1_semantics
#print axioms selected_ct1_trace_exact
#print axioms selected_continue_avoids
#print axioms legacy_counterexample_routes_to_node6
#print axioms node6_work_bounded

end HypostructureParity.Erdos64EG.Node6
