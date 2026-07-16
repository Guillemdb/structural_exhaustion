import StructuralExhaustion.Graph.LocalSeparatorSemanticFrontier
import StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection

namespace StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

namespace Local
export SurplusPatternSemanticLocalProjection (Projection)
end Local

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

/-!
# Strong-semantic obligation frontier

The result retains the exact node-184 projection.  Its obligation only names
the missing downstream theorem appropriate to that literal constructor.
-/

def required : Local.Projection activation normalized →
    LocalSeparatorSemanticFrontier.Obligation
  | .attachmentMismatch .. => .sparseExit
  | .alignedLeftPrefix .. => .fixedCaps
  | .alignedRightPrefix .. => .fixedCaps
  | .cubicRoot .. => .ct3
  | .highRoot .. => .typeB
  | .cubicAfterEdge .. => .ct3
  | .highAfterEdge .. => .typeB

abbrev Pending (projection : Local.Projection activation normalized) :=
  LocalSeparatorSemanticFrontier.Pending _ projection (required activation projection)

def classify (projection : Local.Projection activation normalized) :
    Pending activation projection :=
  LocalSeparatorSemanticFrontier.pending projection (required activation projection)

theorem classify_total (projection : Local.Projection activation normalized) :
    Nonempty (Pending activation projection) :=
  ⟨classify activation projection⟩

theorem classify_retains (projection : Local.Projection activation normalized) :
    (classify activation projection).retained = projection := rfl

theorem classify_obligation_exact
    (projection : Local.Projection activation normalized) :
    (classify activation projection).obligation = required activation projection := rfl

def visibleChecks : Nat := LocalSeparatorSemanticFrontier.visibleChecks

theorem visibleChecks_constant : visibleChecks ≤ 1 :=
  LocalSeparatorSemanticFrontier.visibleChecks_constant

end StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier
