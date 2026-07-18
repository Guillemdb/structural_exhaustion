import StructuralExhaustion.Graph.SurplusPatternAttachmentMismatch

namespace StructuralExhaustion.Examples.SurplusPatternAttachmentMismatch

open StructuralExhaustion Graph

universe u

/-! Theorem-generic transfer: no Erdős-specific target fact is used by the
finite mismatch projection or its exclusive adjacency orientation. -/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable {windowSize remainderSize primitiveSize : Nat}
variable {routed : SurplusPatternCoarseRouting.Routed activation
  windowSize remainderSize primitiveSize}
variable {homogeneous : SurplusPatternCoarseRouting.HomogeneousAudit activation
  windowSize remainderSize primitiveSize routed}
variable {collision : SurplusPatternSemanticBottleneck.Collision activation homogeneous}
variable {trigger : SurplusPatternCoarseRouting.SemanticBottleneckTrigger activation
  collision}

noncomputable example
    (evidence : SurplusPatternSemanticBottleneck.Evidence activation collision
      trigger .attachmentMismatch) :
    SurplusPatternAttachmentMismatch.UnmatchedCoordinateResidual activation
      collision :=
  SurplusPatternAttachmentMismatch.residual activation collision evidence

noncomputable example
    (evidence : SurplusPatternSemanticBottleneck.Evidence activation collision
      trigger .attachmentMismatch) :
    let origin := SurplusPatternAttachmentMismatch.ofEvidence activation
      collision evidence
    origin.firstRoleVertex ≠ origin.secondRoleVertex := by
  dsimp
  exact (SurplusPatternAttachmentMismatch.ofEvidence activation collision
    evidence).roleVertices_ne

end StructuralExhaustion.Examples.SurplusPatternAttachmentMismatch
