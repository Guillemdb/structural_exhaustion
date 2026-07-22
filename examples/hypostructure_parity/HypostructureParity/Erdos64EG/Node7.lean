import Erdos64EG.Node7
import HypostructureErdos64EG.Node7
import HypostructureParity.Erdos64EG.Node6

namespace HypostructureParity.Erdos64EG.Node7

open Hypostructure

universe u

/-!
# Diagram node 7 parity

Node `[7]` is the terminal on node `[6]`'s C1 branch.  The normalized
parity surface is the public target exposed by CT1's generated C1 certificate,
the direct Core closure, and the fact that node `[7]` performs no search beyond
the retained node-`[6]` certificate validation.
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

/-- On the C1 branch, node 7 exposes exactly CT1's public target. -/
theorem selected_powerOfTwoCycle
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node6Focus.Active
        (rootNode6Stage root))
    (isC1 :
      (HypostructureErdos64EG.node6RouteQuery.read
        (rootNode6Stage root) active).terminal = .c1) :
    HypostructureErdos64EG.Target
      (HypostructureErdos64EG.node6ObjectQuery.read
        (rootNode5Stage root) active) :=
  HypostructureErdos64EG.node7_powerOfTwoCycle
    (rootNode6Stage root) active isC1

/-- Node 7's terminal is Core's direct closure of the same public target. -/
theorem selected_direct_closure
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node6Focus.Active
        (rootNode6Stage root))
    (isC1 :
      (HypostructureErdos64EG.node6RouteQuery.read
        (rootNode6Stage root) active).terminal = .c1) :
    (HypostructureErdos64EG.node7
      (rootNode6Stage root) active isC1).mechanism =
        Core.Closure.Mechanism.direct ∧
      HypostructureErdos64EG.Target
        (HypostructureErdos64EG.node6ObjectQuery.read
          (rootNode5Stage root) active) :=
  ⟨HypostructureErdos64EG.node7_closure_mechanism
      (rootNode6Stage root) active isC1,
    (HypostructureErdos64EG.node7
      (rootNode6Stage root) active isC1).proof⟩

/-- The selected C1 route validates exactly one proof-carrying certificate. -/
theorem selected_c1_route_checks_eq_one
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node6Focus.Active
        (rootNode6Stage root))
    (isC1 :
      (HypostructureErdos64EG.node6RouteQuery.read
        (rootNode6Stage root) active).terminal = .c1) :
    (HypostructureErdos64EG.node6RouteQuery.read
      (rootNode6Stage root) active).checks = 1 :=
  HypostructureErdos64EG.node7_route_checks_eq_one
    (rootNode6Stage root) active isC1

/-- Node 7 itself is proof-only after the node-6 C1 route has been selected. -/
theorem node7_work_bounded
    (stage : HypostructureErdos64EG.Node6Stage.{u}) :
    HypostructureErdos64EG.node7WorkBudget.Within stage
      (HypostructureErdos64EG.node7WorkBudget.checks stage) :=
  HypostructureErdos64EG.node7_work_bounded stage

/-- The legacy node-7 C1 terminal is the same target contradiction shape:
the stored public target contradicts the inherited node-5 avoidance fact. -/
theorem legacy_c1_terminal_contradicts {V : Type u}
    (residual : _root_.Erdos64EG.Internal.InitialResidual V)
    (node5 : _root_.Erdos64EG.Internal.Node5Stage residual)
    (run : _root_.StructuralExhaustion.CT1.CertifiedC1Run
      ((_root_.Erdos64EG.Internal.node6Family V).encoding residual node5).spec
      ((_root_.Erdos64EG.Internal.node6Family V).input residual node5)) :
    False :=
  _root_.Erdos64EG.Internal.node7CloseTarget residual node5 run

#print axioms selected_powerOfTwoCycle
#print axioms selected_direct_closure
#print axioms selected_c1_route_checks_eq_one
#print axioms node7_work_bounded
#print axioms legacy_c1_terminal_contradicts

end HypostructureParity.Erdos64EG.Node7
