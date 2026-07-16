import StructuralExhaustion.Graph.LocalSeparatorFirstClause
import StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier

namespace StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Local
export SurplusPatternSemanticLocalProjection (Projection)
end Local

namespace Strong
export SurplusPatternStrongSemanticFrontier (Pending required)
end Strong

namespace Classifier
export SurplusPatternSemanticBottleneck (Collision Residual)
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
variable {normalized : SurplusPatternSemanticNormalization.Result
  activation collision trigger residual frontier}

/-! Exact first local certificate for each retained node-[187] payload. -/

inductive Certificate : Local.Projection activation normalized → Type _ where
  | attachmentMismatch
      (tag_eq : residual.tag = .attachmentMismatch)
      (evidence : SurplusPatternSemanticBottleneck.Evidence activation collision
        trigger .attachmentMismatch) :
      Certificate (.attachmentMismatch tag_eq evidence)
  | alignedLeftPrefix
      (tag_eq : residual.tag = .alignedLeftPrefix)
      (evidence : SurplusPatternSemanticBottleneck.Evidence activation collision
        trigger .alignedLeftPrefix) :
      Certificate (.alignedLeftPrefix tag_eq evidence)
  | alignedRightPrefix
      (tag_eq : residual.tag = .alignedRightPrefix)
      (evidence : SurplusPatternSemanticBottleneck.Evidence activation collision
        trigger .alignedRightPrefix) :
      Certificate (.alignedRightPrefix tag_eq evidence)
  | cubicRoot
      {data : CubicStar.Data ctx.G.object
        (SurplusPatternSemanticConsumer.root (routed := routed))}
      {projection : SurplusPatternSemanticLocalProjection.CubicProjection data}
      (clause : LocalSeparatorFirstClause.Cubic ctx.G.object projection) :
      Certificate (.cubicRoot projection)
  | highRoot
      {degree_ge : 4 ≤ ctx.G.object.degree
        (SurplusPatternSemanticConsumer.root (routed := routed))}
      {projection : SurplusPatternSemanticLocalProjection.HighProjection
        (ctx := ctx) (SurplusPatternSemanticConsumer.root (routed := routed))
        degree_ge}
      (clause : LocalSeparatorFirstClause.High ctx.G.object _ degree_ge projection) :
      Certificate (.highRoot projection)
  | cubicAfterEdge
      {separator : ctx.G.Vertex}
      {data : CubicStar.Data ctx.G.object separator}
      {projection : SurplusPatternSemanticLocalProjection.CubicProjection data}
      (clause : LocalSeparatorFirstClause.Cubic ctx.G.object projection) :
      Certificate (.cubicAfterEdge projection)
  | highAfterEdge
      {separator : ctx.G.Vertex}
      {degree_ge : 4 ≤ ctx.G.object.degree separator}
      {projection : SurplusPatternSemanticLocalProjection.HighProjection
        (ctx := ctx) separator degree_ge}
      (clause : LocalSeparatorFirstClause.High ctx.G.object separator degree_ge
        projection) :
      Certificate (.highAfterEdge projection)

noncomputable def certify (projection : Local.Projection activation normalized) :
    Certificate activation projection := by
  cases projection with
  | attachmentMismatch tagEq evidence =>
      exact .attachmentMismatch tagEq evidence
  | alignedLeftPrefix tagEq evidence =>
      exact .alignedLeftPrefix tagEq evidence
  | alignedRightPrefix tagEq evidence =>
      exact .alignedRightPrefix tagEq evidence
  | cubicRoot projection =>
      exact .cubicRoot (LocalSeparatorFirstClause.cubic ctx.G.object projection)
  | highRoot projection =>
      exact .highRoot (LocalSeparatorFirstClause.high ctx.G.object _ _ projection)
  | cubicAfterEdge projection =>
      exact .cubicAfterEdge
        (LocalSeparatorFirstClause.cubic ctx.G.object projection)
  | highAfterEdge projection =>
      exact .highAfterEdge
        (LocalSeparatorFirstClause.high ctx.G.object _ _ projection)

/-- The exact pending payload and obligation tag are both consumed. -/
structure Result {projection : Local.Projection activation normalized}
    (pending : Strong.Pending activation projection) where
  certificate : Certificate activation pending.retained
  certificateExact : certificate = certify activation pending.retained
  obligationExact : pending.obligation =
    Strong.required activation pending.retained

noncomputable def run {projection : Local.Projection activation normalized}
    (pending : Strong.Pending activation projection) : Result activation pending where
  certificate := certify activation pending.retained
  certificateExact := rfl
  obligationExact := by
    rw [pending.retainedExact]
    exact pending.obligationExact

theorem run_total {projection : Local.Projection activation normalized}
    (pending : Strong.Pending activation projection) :
    Nonempty (Result activation pending) :=
  ⟨run activation pending⟩

def visibleChecks : Nat := LocalSeparatorFirstClause.visibleChecks

theorem visibleChecks_constant : visibleChecks ≤ 4 :=
  LocalSeparatorFirstClause.visibleChecks_constant

end StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause
