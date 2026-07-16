import Erdos64EG.CT9HomogeneousPattern
import StructuralExhaustion.Graph.SurplusPatternCoarseRouting

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact fixed-universe node-144 predecessor classification

The no-overload side is discharged by the already proved quadratic surplus
bound.  On overload, the only search is over the prescribed 49-element
homogeneous pattern and the exact 48-state structural code.  No ambient
vertex, window, attachment, path, pair, or graph universe is enumerated.
-/

noncomputable abbrev geometricActivationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  homogeneousActivationStage ctx

/-- The exact node-[144] output on one predecessor pattern.  Nodes [140],
[142], and [143] already carry the overload and homogeneous audit, so this
record deliberately has no second no-overload branch. -/
structure CoarseBottleneckClassification
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) : Type u where
  collision : Graph.SurplusPatternCoarseRouting.VerifiedCollision
    (geometricActivationStage ctx) homogeneous
  germResidual : Graph.SurplusPatternCoarseRouting.CanonicalGermResidual
    (geometricActivationStage ctx) collision
  semanticTrigger : Graph.SurplusPatternCoarseRouting.SemanticBottleneckTrigger
    (geometricActivationStage ctx) collision

noncomputable def coarseBottleneckClassification
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    CoarseBottleneckClassification ctx overload homogeneous := by
  have large : 48 < (Graph.SurplusPatternCoarseRouting.patternPairs
      (geometricActivationStage ctx) homogeneous).length := by
    rw [Graph.SurplusPatternCoarseRouting.patternPairs_length]
    cases homogeneous <;> norm_num
  let collision := Graph.SurplusPatternCoarseRouting.verifiedCollision
    (geometricActivationStage ctx) homogeneous large
  let germResidual := Graph.SurplusPatternCoarseRouting.canonicalGermResidual
    (geometricActivationStage ctx) collision
  exact {
    collision := collision
    germResidual := germResidual
    semanticTrigger := Graph.SurplusPatternCoarseRouting.toSemanticBottleneckTrigger
      (geometricActivationStage ctx) collision germResidual
  }

/-- The collision branch scans exactly the fixed 49-element homogeneous
pattern and therefore performs at most `49^2 = 2401` coarse-code comparisons.
No graph, window, attachment, path, or context universe enters this count. -/
theorem geometricCollisionChecks_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {routed : Graph.SurplusPatternCoarseRouting.Routed
      (geometricActivationStage ctx) 49 49 49}
    (homogeneous : Graph.SurplusPatternCoarseRouting.HomogeneousAudit
      (geometricActivationStage ctx) 49 49 49 routed) :
    Graph.SurplusPatternCoarseRouting.collisionChecks
      (geometricActivationStage ctx) homogeneous = 2401 := by
  rw [Graph.SurplusPatternCoarseRouting.collisionChecks_eq_square]
  rw [Graph.SurplusPatternCoarseRouting.patternPairs_length]
  cases homogeneous <;> norm_num

/-- Full local work currency at node [144]: 2401 comparisons, at most 4802
coarse-code projections for the uncached runner, and two rooted-germ budgets. -/
theorem geometricClassificationWork_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload))
    (result : CoarseBottleneckClassification ctx overload homogeneous) :
    Graph.SurplusPatternCoarseRouting.classificationWork
      (geometricActivationStage ctx) result.collision =
        7203 + 2 * Graph.SurplusRoutingGerm.zstarBudget
          (coupledOverloadClassRoute ctx 49 49 49 overload).overload.residual.label.1 := by
  rw [Graph.SurplusPatternCoarseRouting.classificationWork_eq]
  rw [Graph.SurplusPatternCoarseRouting.patternPairs_length]
  cases homogeneous <;> norm_num

/-- Verified prefix through the exact finite geometric classification.  This
records the live semantic residual rather than pretending node 144 has been
discharged. -/
structure VerifiedGeometricBottleneckClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedHomogeneousPatternPrefix ctx
  classification : ∀
      (overload : (coupledClassProfile ctx 49 49 49).Overload
        ctx.toBranchContext (coupledClassItems ctx))
      (homogeneous : Graph.SurplusHomogeneousPattern.Audit
        (geometricActivationStage ctx) 49 49 49
        (coupledOverloadClassRoute ctx 49 49 49 overload)),
      Nonempty (CoarseBottleneckClassification ctx overload homogeneous)

noncomputable def verifiedGeometricBottleneckClassificationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedHomogeneousPatternPrefix ctx) :
    VerifiedGeometricBottleneckClassificationPrefix ctx where
  previous := previous
  classification := fun overload homogeneous =>
    ⟨coarseBottleneckClassification ctx overload homogeneous⟩

theorem exists_verifiedGeometricBottleneckClassificationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedGeometricBottleneckClassificationPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedHomogeneousPatternPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedGeometricBottleneckClassificationPrefix ctx previous⟩

end Erdos64EG.Internal
