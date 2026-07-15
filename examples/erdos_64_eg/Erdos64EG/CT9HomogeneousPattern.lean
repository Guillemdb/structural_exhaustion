import Erdos64EG.CT9CoupledClassOverload
import StructuralExhaustion.Graph.SurplusHomogeneousPattern

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9 overload consumer: homogeneous matching--star patterns

This stage consumes the actual overloaded token--role fibre and its exact
window/remainder/primitive constructor route.  The graph layer runs the
reusable greedy matching--star extractor at the threshold belonging to that
class.  No pair, matching, star, path, or graph universe is generated.
-/

noncomputable abbrev homogeneousActivationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  coupledClassActivationStage ctx

noncomputable def homogeneousPatternAudit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat)
    (overload : (coupledClassProfile ctx windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (coupledClassItems ctx)) :=
  Graph.SurplusHomogeneousPattern.audit
    (homogeneousActivationStage ctx)
    windowSize remainderSize primitiveSize
    (coupledOverloadClassRoute ctx windowSize remainderSize primitiveSize overload)

/-- Nodes `[140]`, `[142]`, and `[143]`: whichever class is selected by the
green node-`[139]`/`[141]` route carries a literal matching or star of the
authored size inside the exact overloaded fibre. -/
structure VerifiedHomogeneousPatternPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedCoupledClassOverloadPrefix ctx
  audit : ∀ windowSize remainderSize primitiveSize
      (overload : (coupledClassProfile ctx windowSize remainderSize primitiveSize).Overload
        ctx.toBranchContext (coupledClassItems ctx)),
    Nonempty (Graph.SurplusHomogeneousPattern.Audit
      (homogeneousActivationStage ctx)
      windowSize remainderSize primitiveSize
      (coupledOverloadClassRoute ctx windowSize remainderSize primitiveSize overload))

noncomputable def verifiedHomogeneousPatternPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCoupledClassOverloadPrefix ctx) :
    VerifiedHomogeneousPatternPrefix ctx where
  previous := previous
  audit := fun windowSize remainderSize primitiveSize overload =>
    ⟨homogeneousPatternAudit ctx windowSize remainderSize primitiveSize overload⟩

theorem exists_verifiedHomogeneousPatternPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedHomogeneousPatternPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedCoupledClassOverloadPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedHomogeneousPatternPrefix ctx previous⟩

end Erdos64EG.Internal
