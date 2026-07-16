import StructuralExhaustion.Graph.CubicStar
import StructuralExhaustion.Graph.SurplusPatternSemanticConsumer

namespace StructuralExhaustion.Graph.SurplusPatternSemanticNormalization

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Previous
export SurplusPatternSemanticConsumer (Frontier)
end Previous

namespace Classifier
export SurplusPatternSemanticBottleneck (Collision Evidence Residual ResidualTag)
end Classifier

namespace Coarse
export SurplusPatternCoarseRouting (Routed HomogeneousAudit SemanticBottleneckTrigger)
end Coarse

variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : Coarse.Routed activation windowSize remainderSize primitiveSize}
variable {homogeneous : Coarse.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}

/-!
# Cubic-switch and high-separator normalization

This is a bookkeeping consumer of the exact node-[178] frontier.  Cubic
separator branches are converted to their literal four-vertex star support;
high branches retain the proved degree lower bound.  Mismatch and prefix
branches pass through unchanged.  No quotient, compatible context, response,
fan-safety, Type-B, cap, or target conclusion is added.
-/

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
      (tag_eq : residual.tag = .alignedRootDivergence)
      (evidence : Classifier.Evidence activation collision trigger
        .alignedRootDivergence)
      (data : CubicStar.Data ctx.G.object
        (SurplusPatternSemanticConsumer.root (routed := routed)))
  | highRoot
      (tag_eq : residual.tag = .alignedRootDivergence)
      (evidence : Classifier.Evidence activation collision trigger
        .alignedRootDivergence)
      (degree_ge : 4 ≤ ctx.G.object.degree
        (SurplusPatternSemanticConsumer.root (routed := routed)))
  | cubicAfterEdge
      (tag_eq : residual.tag = .alignedAfterEdgeDivergence)
      (evidence : Classifier.Evidence activation collision trigger
        .alignedAfterEdgeDivergence)
      (separator : ctx.G.Vertex)
      (data : CubicStar.Data ctx.G.object separator)
  | highAfterEdge
      (tag_eq : residual.tag = .alignedAfterEdgeDivergence)
      (evidence : Classifier.Evidence activation collision trigger
        .alignedAfterEdgeDivergence)
      (separator : ctx.G.Vertex)
      (degree_ge : 4 ≤ ctx.G.object.degree separator)

/-- Normalize the exact predecessor result without inspecting any new graph
datum.  `CubicStar.fromRootBranch` and `fromAfterEdgeBranch` only repackage
the already retained incidence and degree proofs. -/
noncomputable def normalize
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
      cases normalized : CubicStar.fromRootBranch ctx.G.object
          data.incidence branch with
      | cubic star => exact .cubicRoot tagEq evidence star
      | high degreeGe => exact .highRoot tagEq evidence degreeGe
  | afterEdgeDivergence tagEq evidence separator incidence branch =>
      cases normalized : CubicStar.fromAfterEdgeBranch ctx.G.object
          incidence branch with
      | cubic star => exact .cubicAfterEdge tagEq evidence separator star
      | high degreeGe => exact .highAfterEdge tagEq evidence separator degreeGe

theorem normalize_total
    (collision : Classifier.Collision activation homogeneous)
    (trigger : Coarse.SemanticBottleneckTrigger activation collision)
    (residual : Classifier.Residual activation collision trigger)
    (frontier : Previous.Frontier activation collision trigger residual) :
    Nonempty (Result activation collision trigger residual frontier) :=
  ⟨normalize activation collision trigger residual frontier⟩

/-- Normalization performs no new primitive inspection. -/
def checks : Nat := 0

theorem checks_eq_zero : checks = 0 := rfl

end StructuralExhaustion.Graph.SurplusPatternSemanticNormalization
