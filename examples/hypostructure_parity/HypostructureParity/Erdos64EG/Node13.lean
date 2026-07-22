import Erdos64EG.Node13
import HypostructureErdos64EG.Node13
import HypostructureParity.Erdos64EG.Node12

namespace HypostructureParity.Erdos64EG.Node13

open Hypostructure

universe u

/-!
# Diagram node 13 parity

The Hypostructure-native node proves the replacement contradiction through
Graph's normalized replacement certificate.  The legacy node proves the
older normalized replacement output directly.
-/

/-- The new node-13 replacement contradiction is read from the newest
framework-owned ledger entry. -/
theorem selected_replacement
    (previous : HypostructureErdos64EG.Node12Stage.{u, u})
    (active :
      HypostructureErdos64EG.Node13Focus.Active
        (HypostructureErdos64EG.node13 previous)) :
    let ctx :=
      HypostructureErdos64EG.node4ContextAtNode12Query.read
        (HypostructureErdos64EG.node13 previous).previous active
    forall (atom : Graph.NormalizedProperBoundariedAtom ctx.G)
      (replacement : Graph.BoundaryPiece atom.toAtom.decomposition.interface),
        Graph.NormalizedAtomReplacementCertificate
          HypostructureErdos64EG.egNormalizedAtomReplacementProfile
          ctx atom replacement -> False :=
  HypostructureErdos64EG.node13_replacement
    (HypostructureErdos64EG.node13 previous) active

/-- Node 13 preserves the production proof-projection work bound. -/
theorem node13_work_bounded
    (previous : HypostructureErdos64EG.Node12Stage.{u, u}) :
    HypostructureErdos64EG.node13WorkBudget.Within previous
      (HypostructureErdos64EG.node13Counted previous).checks :=
  HypostructureErdos64EG.node13Counted_work_bounded previous

/-- The legacy node-13 output is the older normalized replacement statement. -/
theorem legacy_replacement {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (stage : _root_.Erdos64EG.Internal.Node13Stage residual) :
    _root_.Erdos64EG.Internal.Node13Output stage.previous :=
  _root_.Erdos64EG.Internal.node13_replacement stage

/-- The parity record explicitly exposes that node 13 has no manual
application-owned replacement obligation. -/
theorem no_manual_replacement_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈
      HypostructureErdos64EG.node13Metadata.manualObligations) :=
  HypostructureErdos64EG.node13_metadata_has_no_manual_obligation obligation

#print axioms selected_replacement
#print axioms node13_work_bounded
#print axioms legacy_replacement
#print axioms no_manual_replacement_obligation

end HypostructureParity.Erdos64EG.Node13
