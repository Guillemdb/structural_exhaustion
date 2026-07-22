import Erdos64EG.Node12
import HypostructureErdos64EG.Node12
import HypostructureParity.Erdos64EG.Node11

namespace HypostructureParity.Erdos64EG.Node12

open Hypostructure

universe u

/-!
# Diagram node 12 parity

Node `[12]` consumes the literal node-11 residual.  Its normalized
Hypostructure surface is Core's proof-projection certificate for the
context-universality implication of any Graph-certified target-complete
quotient.
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

private noncomputable abbrev rootNode12Stage
    (root : HypostructureErdos64EG.InitialResidual.{u}) :
    HypostructureErdos64EG.Node12Stage.{u, u} :=
  HypostructureErdos64EG.node12 (rootNode11Stage root)

/-- The new node-12 certificate gives the paper-visible context-universality
implication for every identified pair in any certified target-complete
quotient. -/
theorem selected_contextUniversal
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node12Focus.Active
        (rootNode12Stage root))
    (atom : Graph.ProperBoundariedAtom
      (HypostructureErdos64EG.node4ContextAtNode11Query.read
        (rootNode11Stage root) active).G)
    (system : Graph.AtomResponse.CoordinateSystem.{u, u}
      ((HypostructureErdos64EG.node11RegistrationQuery.read
        (rootNode11Stage root) active).family atom)
      HypostructureErdos64EG.Target)
    (quotient : Graph.AtomResponse.TargetCompleteQuotient.{u, u} system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent left right :=
  HypostructureErdos64EG.node12_context_universal
    (rootNode12Stage root) active atom system quotient identified

/-- Every node-12 coordinate system remains attached to Node 11's registered
boundary-degree profile. -/
theorem selected_coordinateProfileRegistered
    (root : HypostructureErdos64EG.InitialResidual.{u})
    (active :
      HypostructureErdos64EG.Node12Focus.Active
        (rootNode12Stage root))
    (atom : Graph.ProperBoundariedAtom
      (HypostructureErdos64EG.node4ContextAtNode11Query.read
        (rootNode11Stage root) active).G)
    (system : Graph.AtomResponse.CoordinateSystem.{u, u}
      ((HypostructureErdos64EG.node11RegistrationQuery.read
        (rootNode11Stage root) active).family atom)
      HypostructureErdos64EG.Target)
    (coordinate : system.Coordinate) :
    system.boundaryDegreeProfile coordinate =
      Graph.BoundariedAtomProfileCertificate.boundaryDegreeProfile
        ((HypostructureErdos64EG.node11RegistrationQuery.read
          (rootNode11Stage root) active).family atom) :=
  HypostructureErdos64EG.node12_coordinate_profile_registered
    (rootNode12Stage root) active atom system coordinate

/-- Node 12 parity preserves the production proof-projection work bound. -/
theorem node12_work_bounded
    (previous : HypostructureErdos64EG.Node11Stage.{u}) :
    HypostructureErdos64EG.node12WorkBudget.Within previous
      (HypostructureErdos64EG.node12Counted previous).checks :=
  HypostructureErdos64EG.node12Counted_work_bounded previous

/-- The legacy node-12 output states the same normalized context-universality
implication on its selected context. -/
theorem legacy_contextUniversal {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (stage : _root_.Erdos64EG.Internal.Node12Stage residual) :
    _root_.Erdos64EG.Internal.Node12Output stage.previous :=
  _root_.Erdos64EG.Internal.node12_context_universal stage

#print axioms selected_contextUniversal
#print axioms selected_coordinateProfileRegistered
#print axioms node12_work_bounded
#print axioms legacy_contextUniversal

end HypostructureParity.Erdos64EG.Node12
