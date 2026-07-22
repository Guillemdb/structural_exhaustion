import Erdos64EG.Node11
import HypostructureErdos64EG.Node11
import HypostructureParity.Erdos64EG.Node10

namespace HypostructureParity.Erdos64EG.Node11

open Hypostructure

universe u

/-!
# Diagram node 11 parity

Node `[11]` consumes the literal node-10 residual.  Its normalized
Hypostructure surface is Graph's generated family of proper boundaried atoms
with uncapped boundary-degree profiles, plus the profile-fibre rejection rule.
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

private noncomputable abbrev rootNode11Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node11Stage.{u} :=
  HypostructureErdos64EG.node11 (rootNode10Stage root)

/-- The new node-11 certificate gives Graph's uncapped boundary-degree
profile on every selected proper boundaried atom. -/
theorem selected_boundaryDegreeProfile
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node11Focus.Active
        (rootNode11Stage root))
    (atom : Graph.ProperBoundariedAtom
      (HypostructureErdos64EG.node4ContextAtNode10Query.read
        (rootNode10Stage root) active).G)
    (vertex : atom.decomposition.interface.Vertex) :
    ((HypostructureErdos64EG.node11RegistrationQuery.read
      (rootNode11Stage root) active).family atom).boundaryDegreeProfile
        vertex =
      atom.decomposition.piece.boundaryDegree vertex :=
  HypostructureErdos64EG.node11_boundaryDegreeProfile
    (rootNode11Stage root) active atom vertex

/-- The new node-11 certificate rejects target-complete identifications
across unequal boundary-degree fibres. -/
theorem selected_profileMismatchRejected
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node11Focus.Active
        (rootNode11Stage root))
    {boundary : Graph.Boundary.{u}}
    {left right : Graph.BoundaryPiece boundary}
    (different : left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) :
    ¬ Graph.BoundaryProfileTargetComplete
      HypostructureErdos64EG.Target left right :=
  HypostructureErdos64EG.node11_profileMismatchRejected
    (rootNode11Stage root) active different

/-- Node 11 parity preserves the production focused-selection work bound. -/
theorem node11_work_bounded
    (previous : HypostructureErdos64EG.Node10Stage.{u}) :
    (HypostructureErdos64EG.node11Counted previous).checks <=
      HypostructureErdos64EG.Node10Focus.selectionBudget.coefficient *
        (HypostructureErdos64EG.Node10Focus.selectionBudget.size previous + 1) ^
          HypostructureErdos64EG.Node10Focus.selectionBudget.degree :=
  HypostructureErdos64EG.node11Counted_work_bounded previous

/-- The legacy node-11 output stores the same paper-visible boundaried-atom
profile family on its selected context. -/
def legacy_boundaryDegreeProfile {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (stage : _root_.Erdos64EG.Internal.Node11Stage residual) :
    _root_.Erdos64EG.Internal.Node11Output stage.previous :=
  _root_.Erdos64EG.Internal.node11_boundaryDegreeProfile stage

#print axioms selected_boundaryDegreeProfile
#print axioms selected_profileMismatchRejected
#print axioms node11_work_bounded
#print axioms legacy_boundaryDegreeProfile

end HypostructureParity.Erdos64EG.Node11
