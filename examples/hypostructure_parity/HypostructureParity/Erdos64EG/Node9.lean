import Erdos64EG.Node9
import HypostructureErdos64EG.Node9
import HypostructureParity.Erdos64EG.Node8

namespace HypostructureParity.Erdos64EG.Node9

open Hypostructure

universe u

/-!
# Diagram node 9 parity

Node `[9]` consumes the literal node-8 residual.  Its normalized
Hypostructure surface is the Graph-owned deletion-criticality certificate:
every edge of the selected minimal counterexample has a degree-three endpoint.
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

/-- The new node-9 certificate gives the paper-visible degree-three endpoint
fact for every edge of the selected context. -/
theorem selected_everyEdgeTouchesDegreeThree
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node9Focus.Active
        (rootNode9Stage root))
    (dart : (HypostructureErdos64EG.node4ContextAtNode8Query.read
      (rootNode8Stage root) active).G.graph.Dart) :
    (HypostructureErdos64EG.node4ContextAtNode8Query.read
      (rootNode8Stage root) active).G.degree dart.fst = 3 ∨
      (HypostructureErdos64EG.node4ContextAtNode8Query.read
        (rootNode8Stage root) active).G.degree dart.snd = 3 :=
  HypostructureErdos64EG.node9_edge_touches_degree_three
    (rootNode9Stage root) active dart

/-- Node 9 parity preserves the production focused-selection work bound. -/
theorem node9_work_bounded
    (previous : HypostructureErdos64EG.Node8Stage.{u}) :
    HypostructureErdos64EG.Node8Focus.selectionBudget.Within previous
      (HypostructureErdos64EG.node9Counted previous).checks :=
  HypostructureErdos64EG.node9Counted_work_bounded previous

/-- The legacy node-9 output states the same paper-visible endpoint predicate
on its selected context. -/
theorem legacy_everyEdgeTouchesDegreeThree {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (stage : _root_.Erdos64EG.Internal.Node9Stage residual) :
    _root_.Erdos64EG.Internal.Node9Output stage.previous :=
  _root_.Erdos64EG.Internal.node9_everyEdgeTouchesDegreeThree stage

#print axioms selected_everyEdgeTouchesDegreeThree
#print axioms node9_work_bounded
#print axioms legacy_everyEdgeTouchesDegreeThree

end HypostructureParity.Erdos64EG.Node9
