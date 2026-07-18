import StructuralExhaustion.Graph.CubicStar
import StructuralExhaustion.Graph.HighSeparatorPortClassification
import StructuralExhaustion.Graph.SurplusPatternSemanticConsumer

namespace StructuralExhaustion.Graph.SurplusPatternDetailedSeparator

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Previous
export SurplusPatternSemanticConsumer (Frontier RootDivergence root)
end Previous

namespace Classifier
export SurplusPatternSemanticBottleneck (Collision Evidence Residual)
end Classifier

namespace Coarse
export SurplusPatternCoarseRouting (Routed HomogeneousAudit SemanticBottleneckTrigger)
end Coarse

variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
variable {homogeneous : Coarse.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}

/-!
# Incidence-preserving separator normalization

The earlier semantic normalization intentionally projects a high separator to
its degree bound.  The port classifier needs the exact root/after-edge
incidences as well.  This result consumes the same exact frontier but preserves
those incidences and immediately executes the finite high-port table.  It adds
no response, compression, fan assignment, safety, or Type-B claim.
-/

structure RootHighData
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed))) where
  ports : HighSeparatorPort.RootHigh ctx.G.object data.incidence third Unit
  table : HighSeparatorPortClassification.RootResult ctx.G.object
    (Previous.root (routed := routed)) ports setup.deletionCritical

noncomputable def rootHighData
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed))) :
    RootHighData (activation := activation) (setup := setup) (routed := routed)
      data third degree_ge := by
  let ports : HighSeparatorPort.RootHigh ctx.G.object data.incidence third Unit :=
    ⟨degree_ge, ()⟩
  exact {
    ports := ports
    table := HighSeparatorPortClassification.classifyRoot ctx.G.object
      (Previous.root (routed := routed)) ports setup.deletionCritical
  }

structure AfterEdgeHighData
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator) where
  ports : HighSeparatorPort.AfterEdgeHigh ctx.G.object incidence Unit
  table : HighSeparatorPortClassification.AfterEdgeResult ctx.G.object separator
    ports setup.deletionCritical

noncomputable def afterEdgeHighData
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator) :
    AfterEdgeHighData (setup := setup) incidence degree_ge := by
  let ports : HighSeparatorPort.AfterEdgeHigh ctx.G.object incidence Unit :=
    ⟨degree_ge, ()⟩
  exact {
    ports := ports
    table := HighSeparatorPortClassification.classifyAfterEdge ctx.G.object
      separator ports setup.deletionCritical
  }

/-- Execute the locally complete square/compatibility/open--open split on the
two divergent root ports.  The recovered third port remains in `classified`
for the later full fan assignment. -/
noncomputable def rootDivergentPairOutcome
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed)))
    (classified : RootHighData (activation := activation) (setup := setup)
      (routed := routed) data third degree_ge) :
    HighSeparatorPortClassification.PairSemanticOutcome ctx.G.object
      (Previous.root (routed := routed)) degree_ge setup.deletionCritical
      classified.ports.leftPort classified.ports.rightPort :=
  HighSeparatorPortClassification.classifyPairSemantics ctx.G.object
    (Previous.root (routed := routed)) degree_ge setup.deletionCritical
    classified.ports.leftPort classified.ports.rightPort
    classified.ports.left_ne_right

/-- After-edge analogue for the two divergent outgoing ports.  The predecessor
port is retained by `classified` and is not silently folded into this pair. -/
noncomputable def afterEdgeDivergentPairOutcome
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator)
    (classified : AfterEdgeHighData (setup := setup) incidence degree_ge) :
    HighSeparatorPortClassification.PairSemanticOutcome ctx.G.object separator
      degree_ge setup.deletionCritical classified.ports.leftPort
      classified.ports.rightPort :=
  HighSeparatorPortClassification.classifyPairSemantics ctx.G.object separator
    degree_ge setup.deletionCritical classified.ports.leftPort
    classified.ports.rightPort classified.ports.left_ne_right

theorem rootDivergentPairOutcome_total
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed)))
    (classified : RootHighData (activation := activation) (setup := setup)
      (routed := routed) data third degree_ge) :
    Nonempty (HighSeparatorPortClassification.PairSemanticOutcome ctx.G.object
      (Previous.root (routed := routed)) degree_ge setup.deletionCritical
      classified.ports.leftPort classified.ports.rightPort) :=
  ⟨rootDivergentPairOutcome (activation := activation) (setup := setup)
    (routed := routed) data third degree_ge classified⟩

theorem afterEdgeDivergentPairOutcome_total
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator)
    (classified : AfterEdgeHighData (setup := setup) incidence degree_ge) :
    Nonempty (HighSeparatorPortClassification.PairSemanticOutcome ctx.G.object
      separator degree_ge setup.deletionCritical classified.ports.leftPort
      classified.ports.rightPort) :=
  ⟨afterEdgeDivergentPairOutcome (setup := setup) incidence degree_ge classified⟩

/-- On the exact activated surplus branch, the direct four-cycle constructors
contradict the inherited target exclusion.  The root-high pair therefore
survives only as a locally compatible pair or a typed open--open endpoint
failure. -/
noncomputable def rootDivergentPairSurvivor
    (data : Previous.RootDivergence (routed := routed))
    (third : RootIncidence.Third ctx.G.object
      (Previous.root (routed := routed)) data.incidence)
    (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed)))
    (classified : RootHighData (activation := activation) (setup := setup)
      (routed := routed) data third degree_ge) :
    HighSeparatorPortClassification.PairSurvivor ctx.G.object
      (Previous.root (routed := routed)) degree_ge setup.deletionCritical
      classified.ports.leftPort classified.ports.rightPort :=
  HighSeparatorPortClassification.classifyPairSurvivor ctx.G.object
    (Previous.root (routed := routed)) degree_ge setup.deletionCritical
    setup.fourFree classified.ports.leftPort classified.ports.rightPort
    classified.ports.left_ne_right

/-- After-edge version of the same target-avoiding survivor split. -/
noncomputable def afterEdgeDivergentPairSurvivor
    {separator : ctx.G.Vertex}
    (incidence : RootIncidence.AfterEdge ctx.G.object separator)
    (degree_ge : 4 ≤ ctx.G.object.degree separator)
    (classified : AfterEdgeHighData (setup := setup) incidence degree_ge) :
    HighSeparatorPortClassification.PairSurvivor ctx.G.object separator
      degree_ge setup.deletionCritical classified.ports.leftPort
      classified.ports.rightPort :=
  HighSeparatorPortClassification.classifyPairSurvivor ctx.G.object separator
    degree_ge setup.deletionCritical setup.fourFree classified.ports.leftPort
    classified.ports.rightPort classified.ports.left_ne_right

inductive Result
    (collision : Classifier.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Classifier.Residual activation collision trigger)
    (frontier : Previous.Frontier activation collision trigger residual) : Type u where
  | attachmentMismatch
      (tag_eq : residual.tag = .attachmentMismatch)
      (evidence : Classifier.Evidence activation collision trigger
        .attachmentMismatch)
  | alignedLeftPrefix
      (tag_eq : residual.tag = .alignedLeftPrefix)
      (evidence : Classifier.Evidence activation collision trigger
        .alignedLeftPrefix)
  | alignedRightPrefix
      (tag_eq : residual.tag = .alignedRightPrefix)
      (evidence : Classifier.Evidence activation collision trigger
        .alignedRightPrefix)
  | cubicRoot
      (data : CubicStar.Data ctx.G.object (Previous.root (routed := routed)))
  | highRoot
      (data : Previous.RootDivergence (routed := routed))
      (third : RootIncidence.Third ctx.G.object
        (Previous.root (routed := routed)) data.incidence)
      (degree_ge : 4 ≤ ctx.G.object.degree (Previous.root (routed := routed)))
      (classified : RootHighData (activation := activation) (setup := setup)
        (routed := routed) data third degree_ge)
  | cubicAfterEdge
      (separator : ctx.G.Vertex)
      (data : CubicStar.Data ctx.G.object separator)
  | highAfterEdge
      (separator : ctx.G.Vertex)
      (incidence : RootIncidence.AfterEdge ctx.G.object separator)
      (degree_ge : 4 ≤ ctx.G.object.degree separator)
      (classified : AfterEdgeHighData (setup := setup) incidence degree_ge)

/-- Preserve every constructor of the exact node-[178] frontier and execute
only the already declared local port table on high leaves. -/
noncomputable def classify
    (collision : Classifier.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Classifier.Residual activation collision trigger)
    (frontier : Previous.Frontier activation collision trigger residual) :
    Result activation collision trigger residual frontier := by
  cases frontier with
  | attachmentMismatch tagEq evidence =>
      exact .attachmentMismatch tagEq evidence
  | alignedLeftPrefix tagEq evidence =>
      exact .alignedLeftPrefix tagEq evidence
  | alignedRightPrefix tagEq evidence =>
      exact .alignedRightPrefix tagEq evidence
  | rootDivergence tagEq evidence data branch =>
      cases branch with
      | cubic degreeEq third =>
          exact .cubicRoot
            (CubicStar.ofRootDivergence ctx.G.object data.incidence third degreeEq)
      | high degreeGe third =>
          exact .highRoot data third degreeGe
            (rootHighData (activation := activation) (setup := setup)
              (routed := routed) data third degreeGe)
  | afterEdgeDivergence tagEq evidence separator incidence branch =>
      cases branch with
      | cubic degreeEq =>
          exact .cubicAfterEdge separator
            (CubicStar.ofAfterEdge ctx.G.object incidence degreeEq)
      | high degreeGe =>
          exact .highAfterEdge separator incidence degreeGe
            (afterEdgeHighData (setup := setup) incidence degreeGe)

theorem classify_total
    (collision : Classifier.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Classifier.Residual activation collision trigger)
    (frontier : Previous.Frontier activation collision trigger residual) :
    Nonempty (Result activation collision trigger residual frontier) :=
  ⟨classify activation collision trigger residual frontier⟩

/-- The detailed normalization adds no graph search.  A high leaf executes one
fixed ten-predicate table; all incidence and cubic data are proof projections. -/
def checks : Nat := HighSeparatorPortClassification.pairSemanticChecks

theorem checks_eq_ten : checks = 10 :=
  HighSeparatorPortClassification.pairSemanticChecks_eq_ten

end StructuralExhaustion.Graph.SurplusPatternDetailedSeparator
