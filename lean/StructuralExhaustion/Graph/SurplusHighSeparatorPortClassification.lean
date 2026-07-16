import StructuralExhaustion.Graph.HighSeparatorPortClassification
import StructuralExhaustion.Graph.SurplusHighSeparatorPort

namespace StructuralExhaustion.Graph.SurplusHighSeparatorPortClassification

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

abbrev Token := SurplusRoutingGerm.Token (ctx := ctx) (setup := setup)

/-- A classified root-high result with the exact classified-germ source kept
as provenance. -/
structure RootResult
    {token : Token (ctx := ctx) (setup := setup)}
    (source : SurplusRoutingGerm.ClassifiedRootDivergence token) where
  third : RootIncidence.Third ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
    source.divergence
  output : HighSeparatorPort.RootHigh ctx.G.object source.divergence third
    (SurplusRoutingGerm.ClassifiedRootDivergence token)
  table : HighSeparatorPortClassification.RootResult ctx.G.object
    (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
    output setup.deletionCritical

noncomputable def rootTable?
    {token : Token (ctx := ctx) (setup := setup)}
    (source : SurplusRoutingGerm.ClassifiedRootDivergence token) :
    Option (RootResult source) :=
  match SurplusHighSeparatorPort.rootPorts? source with
  | none => none
  | some packed => some {
      third := packed.1
      output := packed.2
      table := HighSeparatorPortClassification.classifyRoot ctx.G.object
        (SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token)
        packed.2 setup.deletionCritical
    }

/-- An after-edge result with the complete classified incidence retained. -/
structure AfterEdgeResult
    {token : Token (ctx := ctx) (setup := setup)}
    (source : SurplusRoutingGerm.ClassifiedAfterEdgeIncidence token) where
  output : HighSeparatorPort.AfterEdgeHigh ctx.G.object source.incidence
    (SurplusRoutingGerm.ClassifiedAfterEdgeIncidence token)
  table : HighSeparatorPortClassification.AfterEdgeResult ctx.G.object
    source.separator output setup.deletionCritical

noncomputable def afterEdgeTable?
    {token : Token (ctx := ctx) (setup := setup)}
    (source : SurplusRoutingGerm.ClassifiedAfterEdgeIncidence token) :
    Option (AfterEdgeResult source) :=
  match SurplusHighSeparatorPort.afterEdgePorts? source with
  | none => none
  | some output => some {
      output := output
      table := HighSeparatorPortClassification.classifyAfterEdge ctx.G.object
        source.separator output setup.deletionCritical
    }

/-- Two exact port-type tests plus the bounded compatibility-field table. -/
def checks : Nat := HighSeparatorPortClassification.checks

end StructuralExhaustion.Graph.SurplusHighSeparatorPortClassification
