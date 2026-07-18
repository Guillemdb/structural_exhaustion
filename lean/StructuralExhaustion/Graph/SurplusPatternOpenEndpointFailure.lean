import StructuralExhaustion.Graph.HighOpenEndpointFailure
import StructuralExhaustion.Graph.SurplusPatternDetailedSeparator

namespace StructuralExhaustion.Graph.SurplusPatternOpenEndpointFailure

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Previous
export SurplusPatternSemanticConsumer (RootDivergence root)
end Previous

namespace Coarse
export SurplusPatternCoarseRouting (Routed HomogeneousAudit)
end Coarse

variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
variable {homogeneous : Coarse.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}

structure RootFailureLeaf
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed))) where
  classified : SurplusPatternDetailedSeparator.RootHighData
    (activation := activation) (setup := setup) (routed := routed)
      data third degree_ge
  failure : HighSeparatorPortClassification.OpenEndpointFailure ctx.G.object
    (Previous.root (routed := routed)) degree_ge setup.deletionCritical
    classified.ports.leftPort classified.ports.rightPort

noncomputable def activateRoot
    {data : Previous.RootDivergence (routed := routed)}
    {third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence}
    {degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed))}
    (leaf : RootFailureLeaf (activation := activation) (setup := setup)
      (routed := routed) data third degree_ge) :
    HighOpenEndpointFailure.ActivatedFailure input ctx
      (Previous.root (routed := routed)) degree_ge setup.deletionCritical
      leaf.classified.ports.leftPort leaf.classified.ports.rightPort :=
  HighOpenEndpointFailure.activate input ctx setup.minimumDegree_eq_three
    (Previous.root (routed := routed)) degree_ge setup.deletionCritical
    leaf.failure

structure AfterEdgeFailureLeaf
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator) where
  classified : SurplusPatternDetailedSeparator.AfterEdgeHighData
    (setup := setup) incidence degree_ge
  failure : HighSeparatorPortClassification.OpenEndpointFailure ctx.G.object
    separator degree_ge setup.deletionCritical classified.ports.leftPort
    classified.ports.rightPort

noncomputable def activateAfterEdge
    {separator : ctx.G.Vertex}
    {incidence : RootIncidence.AfterEdge ctx.G.object separator}
    {degree_ge : 4 ≤ ctx.G.object.degree separator}
    (leaf : AfterEdgeFailureLeaf (setup := setup) incidence degree_ge) :
    HighOpenEndpointFailure.ActivatedFailure input ctx separator degree_ge
      setup.deletionCritical leaf.classified.ports.leftPort
      leaf.classified.ports.rightPort :=
  HighOpenEndpointFailure.activate input ctx setup.minimumDegree_eq_three
    separator degree_ge setup.deletionCritical leaf.failure

/-- The smallest residual: local blocker/response activation is complete, but
the exact selected active slots are not part of the separator source. -/
structure ActivationFrontier
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    (activatedFailure : HighOpenEndpointFailure.ActivatedFailure input ctx center centerHigh
      setup.deletionCritical first second) : Type u where
  activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
    centerHigh setup.deletionCritical first second := activatedFailure

/-- Exact consumer needed before the literal shared carrier may be inserted
into the selected-demand blocker ledger. -/
structure SelectedSlotEntry
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    {activatedFailure : HighOpenEndpointFailure.ActivatedFailure input ctx center centerHigh
      setup.deletionCritical first second}
    (_frontier : ActivationFrontier (setup := setup) activatedFailure) : Type u where
  firstSlot : SurplusPortActivation.Slot setup
  secondSlot : SurplusPortActivation.Slot setup
  firstCenter : firstSlot.1 = center
  secondCenter : secondSlot.1 = center
  firstEndpointExact : SurplusPortActivity.portEndpoint ctx.G.object firstSlot =
    HighCenterPort.endpoint ctx.G.object center first
  secondEndpointExact : SurplusPortActivity.portEndpoint ctx.G.object secondSlot =
    HighCenterPort.endpoint ctx.G.object center second

end StructuralExhaustion.Graph.SurplusPatternOpenEndpointFailure
