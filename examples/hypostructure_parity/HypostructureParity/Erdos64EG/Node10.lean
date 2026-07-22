import Erdos64EG.Node10
import HypostructureErdos64EG.Node10
import HypostructureParity.Erdos64EG.Node9

namespace HypostructureParity.Erdos64EG.Node10

open Hypostructure

universe u

/-!
# Diagram node 10 parity

Node `[10]` consumes the literal node-9 residual.  Its normalized
Hypostructure surface is Graph's registered slack-vertex independence
consequence: vertices of degree at least four are independent.
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

private noncomputable abbrev rootNode6AvoidingStage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node6AvoidingStage.{u} :=
  HypostructureErdos64EG.node6ContinueAvoiding (rootNode6Stage root)

private noncomputable abbrev rootNode8Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node8Stage.{u} :=
  HypostructureErdos64EG.node8 (rootNode6AvoidingStage root)

private noncomputable abbrev rootNode9Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node9Stage.{u} :=
  HypostructureErdos64EG.node9 (rootNode8Stage root)

private noncomputable abbrev rootNode10Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node10Stage.{u} :=
  HypostructureErdos64EG.node10 (rootNode9Stage root)

/-- The new node-10 certificate gives the paper-visible high-degree
independence fact on the selected context. -/
theorem selected_highDegreeVerticesIndependent
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node10Focus.Active
        (rootNode10Stage root))
    {left right : (HypostructureErdos64EG.node4ContextAtNode9Query.read
      (rootNode9Stage root) active).G.Vertex}
    (leftHigh :
      4 ≤ (HypostructureErdos64EG.node4ContextAtNode9Query.read
        (rootNode9Stage root) active).G.degree left)
    (rightHigh :
      4 ≤ (HypostructureErdos64EG.node4ContextAtNode9Query.read
        (rootNode9Stage root) active).G.degree right) :
    Not ((HypostructureErdos64EG.node4ContextAtNode9Query.read
      (rootNode9Stage root) active).G.graph.Adj left right) :=
  HypostructureErdos64EG.node10_high_degree_vertices_independent
    (rootNode10Stage root) active leftHigh rightHigh

/-- Node 10 parity preserves the production focused-selection work bound. -/
theorem node10_work_bounded
    (previous : HypostructureErdos64EG.Node9Stage.{u}) :
    (HypostructureErdos64EG.node10Counted previous).checks <=
      HypostructureErdos64EG.Node9Focus.selectionBudget.coefficient *
        (HypostructureErdos64EG.Node9Focus.selectionBudget.size previous + 1) ^
          HypostructureErdos64EG.Node9Focus.selectionBudget.degree :=
  HypostructureErdos64EG.node10Counted_work_bounded previous

/-- The legacy node-10 output states the same paper-visible high-degree
independence predicate on its selected context. -/
theorem legacy_highDegreeVerticesIndependent {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (stage : _root_.Erdos64EG.Internal.Node10Stage residual) :
    _root_.Erdos64EG.Internal.Node10Output stage.previous :=
  _root_.Erdos64EG.Internal.node10_highDegreeVerticesIndependent stage

#print axioms selected_highDegreeVerticesIndependent
#print axioms node10_work_bounded
#print axioms legacy_highDegreeVerticesIndependent

end HypostructureParity.Erdos64EG.Node10
