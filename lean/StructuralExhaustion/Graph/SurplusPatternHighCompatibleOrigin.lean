import StructuralExhaustion.Graph.HighCompatiblePortOrigin
import StructuralExhaustion.Graph.SurplusPatternDetailedSeparator

namespace StructuralExhaustion.Graph.SurplusPatternHighCompatibleOrigin

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

/-- A compatible root-high leaf with the complete recovered-incidence source
retained.  Compatibility is the exact result of the preceding local table. -/
structure RootCompatibleLeaf
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree
      (Previous.root (routed := routed))) where
  classified : SurplusPatternDetailedSeparator.RootHighData
    (activation := activation) (setup := setup)
    (routed := routed) data third degree_ge
  compatible : HighCenterPort.FanCompatible ctx.G.object
    (Previous.root (routed := routed)) classified.ports.leftPort
    classified.ports.rightPort

/-- Exact refinement of a root-compatible leaf into open origin or the
separate triangular-compatible residual. -/
noncomputable def classifyRoot
    {data : Previous.RootDivergence (routed := routed)}
    {third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence}
    {degree_ge : 4 ≤ ctx.G.object.degree
      (Previous.root (routed := routed))}
    (leaf : RootCompatibleLeaf (activation := activation) (setup := setup)
      (routed := routed) data third degree_ge) :
    HighCompatiblePortOrigin.Outcome ctx.G.object
      (Previous.root (routed := routed)) degree_ge
      setup.deletionCritical leaf.classified.ports.leftPort
      leaf.classified.ports.rightPort :=
  HighCompatiblePortOrigin.classify ctx.G.object
    (Previous.root (routed := routed)) degree_ge setup.deletionCritical
    leaf.classified.ports.leftPort leaf.classified.ports.rightPort
    leaf.classified.ports.left_ne_right leaf.compatible

/-- After-edge analogue, retaining the predecessor incidence and both outgoing
ports in the same detailed source object. -/
structure AfterEdgeCompatibleLeaf
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator) where
  classified : SurplusPatternDetailedSeparator.AfterEdgeHighData
    (setup := setup) incidence degree_ge
  compatible : HighCenterPort.FanCompatible ctx.G.object separator
    classified.ports.leftPort classified.ports.rightPort

noncomputable def classifyAfterEdge
    {separator : ctx.G.Vertex}
    {incidence : RootIncidence.AfterEdge ctx.G.object separator}
    {degree_ge : 4 ≤ ctx.G.object.degree separator}
    (leaf : AfterEdgeCompatibleLeaf (setup := setup) incidence degree_ge) :
    HighCompatiblePortOrigin.Outcome ctx.G.object separator degree_ge
      setup.deletionCritical leaf.classified.ports.leftPort
      leaf.classified.ports.rightPort :=
  HighCompatiblePortOrigin.classify ctx.G.object separator degree_ge
    setup.deletionCritical leaf.classified.ports.leftPort
    leaf.classified.ports.rightPort leaf.classified.ports.left_ne_right
    leaf.compatible

theorem classifyRoot_total
    {data : Previous.RootDivergence (routed := routed)}
    {third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence}
    {degree_ge : 4 ≤ ctx.G.object.degree
      (Previous.root (routed := routed))}
    (leaf : RootCompatibleLeaf (activation := activation) (setup := setup)
      (routed := routed) data third degree_ge) :
    Nonempty (HighCompatiblePortOrigin.Outcome ctx.G.object
      (Previous.root (routed := routed)) degree_ge
      setup.deletionCritical leaf.classified.ports.leftPort
      leaf.classified.ports.rightPort) :=
  ⟨classifyRoot (activation := activation) leaf⟩

theorem classifyAfterEdge_total
    {separator : ctx.G.Vertex}
    {incidence : RootIncidence.AfterEdge ctx.G.object separator}
    {degree_ge : 4 ≤ ctx.G.object.degree separator}
    (leaf : AfterEdgeCompatibleLeaf (setup := setup) incidence degree_ge) :
    Nonempty (HighCompatiblePortOrigin.Outcome ctx.G.object separator degree_ge
      setup.deletionCritical leaf.classified.ports.leftPort
      leaf.classified.ports.rightPort) :=
  ⟨classifyAfterEdge leaf⟩

end StructuralExhaustion.Graph.SurplusPatternHighCompatibleOrigin
