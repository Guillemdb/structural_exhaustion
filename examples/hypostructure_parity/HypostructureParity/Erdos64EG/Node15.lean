import Erdos64EG.Node15
import HypostructureErdos64EG.Node15
import HypostructureParity.Erdos64EG.Node14

namespace HypostructureParity.Erdos64EG.Node15

open Hypostructure

universe u

/-!
# Diagram node 15 parity

The legacy node `[15]` records an exhaustive `P13`-free / not-`P13`-free
decision.  The Hypostructure-native node realizes the same paper split through
focused CT1 with the graph layer's generic induced-obstruction target
specialized to `P13`: CT1's C1 terminal feeds the packing branch and its
avoiding terminal is the `P13`-free branch.
-/

/-- The new node-15 CT1 terminal has exactly the induced-`P13` /
induced-`P13`-free meaning. -/
theorem selected_semantics
    (previous : HypostructureErdos64EG.Node14Stage.{u, u})
    (active :
      HypostructureErdos64EG.Node15Focus.Active
        (HypostructureErdos64EG.node15 previous)) :
    match
        (HypostructureErdos64EG.node15Encoding.{u, u}.routeQuery.read
          (HypostructureErdos64EG.node15 previous) active).terminal with
    | .c1 =>
        Hypostructure.Graph.HasInducedObstruction
          HypostructureErdos64EG.p13Obstruction
          (HypostructureErdos64EG.node15ObjectQuery.read
            (HypostructureErdos64EG.node15 previous).previous active)
    | .avoiding =>
        Hypostructure.Graph.InducedObstructionFree
          HypostructureErdos64EG.p13Obstruction
          (HypostructureErdos64EG.node15ObjectQuery.read
            (HypostructureErdos64EG.node15 previous).previous active) :=
  HypostructureErdos64EG.node15_semantics
    (HypostructureErdos64EG.node15 previous) active

/-- The new avoiding continuation is the paper's `P13`-free branch. -/
theorem selected_p13_free_branch
    (stage : HypostructureErdos64EG.node15Encoding.{u, u}.AvoidingStage)
    (active :
      HypostructureErdos64EG.node15Encoding.{u, u}.AvoidingProfile.Active
        stage) :
    Hypostructure.Graph.InducedObstructionFree
      HypostructureErdos64EG.p13Obstruction
      (HypostructureErdos64EG.node15ObjectQuery.read
        stage.previous.previous active) :=
  HypostructureErdos64EG.node15_p13_free stage active

/-- Node 15 parity preserves the production focused CT1 work bound. -/
theorem node15_work_bounded
    (previous : HypostructureErdos64EG.Node14Stage.{u, u}) :
    HypostructureErdos64EG.node15Encoding.{u, u}.workBudget.Within previous
      (HypostructureErdos64EG.node15Counted previous).checks :=
  HypostructureErdos64EG.node15Counted_work_bounded previous

/-- The legacy node-15 decision is exhaustive in its older decision encoding. -/
theorem legacy_exhaustive {V : Type u}
    {residual : _root_.Erdos64EG.Internal.InitialResidual V}
    (input : _root_.Erdos64EG.Internal.Node15Input residual) :
    Nonempty (_root_.Erdos64EG.Internal.Node15Decision residual) :=
  _root_.Erdos64EG.Internal.node15_exhaustive input

/-- The parity record exposes that node 15 has no application-owned manual
obligation. -/
theorem no_manual_p13_decision_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈
      HypostructureErdos64EG.node15Metadata.manualObligations) :=
  HypostructureErdos64EG.node15_metadata_has_no_manual_obligation obligation

#print axioms selected_semantics
#print axioms selected_p13_free_branch
#print axioms node15_work_bounded
#print axioms legacy_exhaustive
#print axioms no_manual_p13_decision_obligation

end HypostructureParity.Erdos64EG.Node15
