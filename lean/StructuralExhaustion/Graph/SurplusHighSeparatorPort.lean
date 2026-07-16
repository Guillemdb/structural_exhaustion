import StructuralExhaustion.Graph.HighSeparatorPort
import StructuralExhaustion.Graph.SurplusRoutingGerm

namespace StructuralExhaustion.Graph.SurplusHighSeparatorPort

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

abbrev Token := SurplusRoutingGerm.Token (ctx := ctx) (setup := setup)

/-- Root-high port recovery retaining the complete currently classified source
as opaque provenance.  No fields absent from that source are claimed. -/
noncomputable def rootPorts?
    {token : Token (ctx := ctx) (setup := setup)}
    (source : SurplusRoutingGerm.ClassifiedRootDivergence token) :=
  HighSeparatorPort.ofRootBranch? ctx.G.object source.divergence
    (SurplusRoutingGerm.ClassifiedRootDivergence token) source source.branch

/-- After-edge-high port recovery retaining the complete currently classified
source as opaque provenance. -/
noncomputable def afterEdgePorts?
    {token : Token (ctx := ctx) (setup := setup)}
    (source : SurplusRoutingGerm.ClassifiedAfterEdgeIncidence token) :=
  HighSeparatorPort.ofAfterEdgeBranch? ctx.G.object source.incidence
    (SurplusRoutingGerm.ClassifiedAfterEdgeIncidence token) source
    source.degreeBranch

end StructuralExhaustion.Graph.SurplusHighSeparatorPort
