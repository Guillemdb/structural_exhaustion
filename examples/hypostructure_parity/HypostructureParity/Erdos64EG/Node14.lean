import Erdos64EG.Node14
import HypostructureErdos64EG.Node14
import HypostructureParity.Erdos64EG.Node13

namespace HypostructureParity.Erdos64EG.Node14

open Hypostructure

universe u

/-!
# Diagram node 14 parity

Node `[14]` derives hereditary target-uncompressibility from node `[13]`
replacement and node `[12]` context-universality.  The Hypostructure-native
surface is Graph's normalized uncompressibility corollary over the literal
node-13 residual.
-/

/-- The new node-14 corollary excludes every normalized target-complete
replacement compression. -/
theorem selected_noTargetCompleteCompression
    (previous : HypostructureErdos64EG.Node13Stage.{u, u})
    (active :
      HypostructureErdos64EG.Node14Focus.Active
        (HypostructureErdos64EG.node14 previous)) :
    let ctx :=
      HypostructureErdos64EG.node4ContextAtNode13Query.read
        (HypostructureErdos64EG.node14 previous).previous active
    forall (atom : Graph.NormalizedProperBoundariedAtom ctx.G)
      (replacement : Graph.BoundaryPiece atom.toAtom.decomposition.interface),
        Graph.NormalizedAtomReplacementCertificate
          HypostructureErdos64EG.egNormalizedAtomReplacementProfile
          ctx atom replacement -> False :=
  HypostructureErdos64EG.node14_noTargetCompleteCompression
    (HypostructureErdos64EG.node14 previous) active

/-- The new node-14 corollary turns a failed context-universality test into
a target-defective, non-target-complete identification. -/
theorem selected_defectiveIdentification
    (previous : HypostructureErdos64EG.Node13Stage.{u, u})
    (active :
      HypostructureErdos64EG.Node14Focus.Active
        (HypostructureErdos64EG.node14 previous)) :
    forall (atom : Graph.ProperBoundariedAtom
      (HypostructureErdos64EG.node4ContextAtNode13Query.read
        (HypostructureErdos64EG.node14 previous).previous active).G)
      (system : Graph.AtomResponse.CoordinateSystem.{u, u}
        ((HypostructureErdos64EG.node11RegistrationAtNode13Query.read
          (HypostructureErdos64EG.node14 previous).previous active).family
          atom) HypostructureErdos64EG.Target)
      {left right : system.Coordinate},
        Not (system.ContextEquivalent left right) ->
          Not (Graph.AtomResponse.TargetCompleteIdentification system
            left right) ∧
            Graph.AtomResponse.TargetDefect system left right :=
  HypostructureErdos64EG.node14_defectiveIdentification
    (HypostructureErdos64EG.node14 previous) active

/-- Node 14 parity preserves the production proof-projection work bound. -/
theorem node14_work_bounded
    (previous : HypostructureErdos64EG.Node13Stage.{u, u}) :
    HypostructureErdos64EG.node14WorkBudget.Within previous
      (HypostructureErdos64EG.node14Counted previous).checks :=
  HypostructureErdos64EG.node14Counted_work_bounded previous

/-- The legacy node-14 output records the older hereditary
target-uncompressibility statement. -/
theorem legacy_uncompressible {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (stage : _root_.Erdos64EG.Internal.Node14Stage residual) :
    _root_.Erdos64EG.Internal.Node14Output stage.previous :=
  _root_.Erdos64EG.Internal.node14_uncompressible stage

/-- The parity record exposes that node 14 has no application-owned manual
obligation. -/
theorem no_manual_uncompressibility_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈
      HypostructureErdos64EG.node14Metadata.manualObligations) :=
  HypostructureErdos64EG.node14_metadata_has_no_manual_obligation obligation

#print axioms selected_noTargetCompleteCompression
#print axioms selected_defectiveIdentification
#print axioms node14_work_bounded
#print axioms legacy_uncompressible
#print axioms no_manual_uncompressibility_obligation

end HypostructureParity.Erdos64EG.Node14

