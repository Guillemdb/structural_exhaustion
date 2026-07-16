import StructuralExhaustion.Graph.LocalSeparatorProjection
import StructuralExhaustion.Graph.SurplusPatternSemanticNormalization

namespace StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Normalized
export SurplusPatternSemanticNormalization (Result)
end Normalized

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
variable {collision : Classifier.Collision activation homogeneous}
variable {trigger : Coarse.SemanticBottleneckTrigger activation collision}
variable {residual : Classifier.Residual activation collision trigger}
variable {frontier : SurplusPatternSemanticConsumer.Frontier
  activation collision trigger residual}

/-!
# Literal local projections after separator normalization

The cubic branch exposes its exact three-boundary switch shape.  The high
branch exposes only the actual declared incident-port schedule and its
cardinality.  Neither projection carries response or target semantics.
-/

abbrev CubicProjection {center : ctx.G.Vertex}
    (data : CubicStar.Data ctx.G.object center) :=
  LocalSeparatorProjection.Cubic ctx.G.object data

abbrev HighProjection (center : ctx.G.Vertex)
    (degree_ge : 4 ≤ ctx.G.object.degree center) :=
  LocalSeparatorProjection.High ctx.G.object center degree_ge

inductive Projection
    (normalized : Normalized.Result activation collision trigger residual frontier) :
    Type _ where
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
      {data : CubicStar.Data ctx.G.object
        (SurplusPatternSemanticConsumer.root (routed := routed))}
      (projection : CubicProjection data)
  | highRoot
      {degree_ge : 4 ≤ ctx.G.object.degree
        (SurplusPatternSemanticConsumer.root (routed := routed))}
      (projection : HighProjection (ctx := ctx)
        (SurplusPatternSemanticConsumer.root (routed := routed)) degree_ge)
  | cubicAfterEdge
      {separator : ctx.G.Vertex}
      {data : CubicStar.Data ctx.G.object separator}
      (projection : CubicProjection data)
  | highAfterEdge
      {separator : ctx.G.Vertex}
      {degree_ge : 4 ≤ ctx.G.object.degree separator}
      (projection : HighProjection (ctx := ctx) separator degree_ge)

noncomputable def project
    (normalized : Normalized.Result activation collision trigger residual frontier) :
    Projection activation normalized := by
  cases normalized with
  | attachmentMismatch tagEq evidence =>
      exact .attachmentMismatch tagEq evidence
  | alignedLeftPrefix tagEq evidence =>
      exact .alignedLeftPrefix tagEq evidence
  | alignedRightPrefix tagEq evidence =>
      exact .alignedRightPrefix tagEq evidence
  | cubicRoot tagEq evidence data =>
      exact .cubicRoot (LocalSeparatorProjection.cubic ctx.G.object data)
  | highRoot tagEq evidence degreeGe =>
      exact .highRoot (LocalSeparatorProjection.high ctx.G.object _ degreeGe)
  | cubicAfterEdge tagEq evidence separator data =>
      exact .cubicAfterEdge (LocalSeparatorProjection.cubic ctx.G.object data)
  | highAfterEdge tagEq evidence separator degreeGe =>
      exact .highAfterEdge
        (LocalSeparatorProjection.high ctx.G.object separator degreeGe)

theorem project_total
    (normalized : Normalized.Result activation collision trigger residual frontier) :
    Nonempty (Projection activation normalized) :=
  ⟨project activation normalized⟩

/-- A high projection may materialize only the one selected centre's declared
neighbour order; charge at most one adjacency check per ambient vertex. -/
def visibleChecks : Nat := LocalSeparatorProjection.visibleChecks ctx.G.object

theorem visibleChecks_linear : visibleChecks (ctx := ctx) ≤
    ctx.G.object.input.vertices.card :=
  LocalSeparatorProjection.visibleChecks_linear ctx.G.object

end StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection
