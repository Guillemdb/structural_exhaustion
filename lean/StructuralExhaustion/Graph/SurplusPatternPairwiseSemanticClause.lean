import StructuralExhaustion.Graph.LocalSeparatorPairwiseClause
import StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause

namespace StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Strong
export SurplusPatternStrongSemanticFrontier (Pending required)
end Strong

namespace First
export SurplusPatternFirstSemanticClause (Certificate Result)
end First

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
variable {projection : SurplusPatternSemanticLocalProjection.Projection
  activation normalized}
variable {pending : Strong.Pending activation projection}

/-- Exact clause type justified by one node-[190] certificate. -/
def Clause {localProjection : SurplusPatternSemanticLocalProjection.Projection
    activation normalized} : First.Certificate activation localProjection → Prop
  | .attachmentMismatch .. => True
  | .alignedLeftPrefix .. => True
  | .alignedRightPrefix .. => True
  | .cubicRoot first => LocalSeparatorPairwiseClause.Cubic ctx.G.object first
  | .highRoot first => LocalSeparatorPairwiseClause.High ctx.G.object first
  | .cubicAfterEdge first => LocalSeparatorPairwiseClause.Cubic ctx.G.object first
  | .highAfterEdge first => LocalSeparatorPairwiseClause.High ctx.G.object first

def derive {localProjection : SurplusPatternSemanticLocalProjection.Projection
    activation normalized} (certificate : First.Certificate activation localProjection) :
    Clause activation certificate := by
  cases certificate with
  | attachmentMismatch => trivial
  | alignedLeftPrefix => trivial
  | alignedRightPrefix => trivial
  | cubicRoot first => exact LocalSeparatorPairwiseClause.cubic ctx.G.object first
  | highRoot first => exact LocalSeparatorPairwiseClause.high ctx.G.object first
  | cubicAfterEdge first =>
      exact LocalSeparatorPairwiseClause.cubic ctx.G.object first
  | highAfterEdge first =>
      exact LocalSeparatorPairwiseClause.high ctx.G.object first

/-- Consume the exact node-[190] certificate while retaining its still-pending
semantic obligation unchanged. -/
structure Result (first : First.Result activation pending) where
  clause : Clause activation first.certificate
  clauseExact : clause = derive activation first.certificate
  obligationExact : pending.obligation = Strong.required activation pending.retained

def run (first : First.Result activation pending) : Result activation first where
  clause := derive activation first.certificate
  clauseExact := rfl
  obligationExact := first.obligationExact

theorem run_total (first : First.Result activation pending) :
    Nonempty (Result activation first) := ⟨run activation first⟩

def visibleChecks : Nat := LocalSeparatorPairwiseClause.visibleChecks

theorem visibleChecks_eq_zero : visibleChecks = 0 :=
  LocalSeparatorPairwiseClause.visibleChecks_eq_zero

end StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause
