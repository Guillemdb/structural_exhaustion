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

/-- Nodes `[140]`, `[142]`, and `[143]` obligations accumulated on the exact
coupled-overload CT9 ledger. -/
structure HomogeneousPatternFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  audit : ∀ windowSize remainderSize primitiveSize
      (overload : (coupledClassProfile ctx windowSize remainderSize primitiveSize).Overload
        ctx.toBranchContext (coupledClassItems ctx)),
    Nonempty (Graph.SurplusHomogeneousPattern.Audit
      (homogeneousActivationStage ctx)
      windowSize remainderSize primitiveSize
      (coupledOverloadClassRoute ctx windowSize remainderSize primitiveSize overload))

abbrev HomogeneousPatternLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCoupledClassOverloadPrefix ctx) :=
  Core.Routing.LedgerExtension
    (CoupledClassOverloadLedger ctx previous.1)
    (fun _ledger => HomogeneousPatternFacts ctx)

abbrev VerifiedHomogeneousPatternPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedCoupledClassOverloadPrefix ctx =>
    Core.Routing.ResidualStage .ct9 (HomogeneousPatternLedger ctx previous)

noncomputable def verifiedHomogeneousPatternPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCoupledClassOverloadPrefix ctx) :
    VerifiedHomogeneousPatternPrefix ctx :=
  let stage := (coupledClassOverloadLedgerStage ctx previous).extend {
    audit := fun windowSize remainderSize primitiveSize overload =>
      ⟨homogeneousPatternAudit ctx windowSize remainderSize primitiveSize overload⟩
  }
  ⟨previous, stage⟩

/-- Canonical complete CT9 stage after the homogeneous-pattern consumers. -/
noncomputable def homogeneousPatternLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedHomogeneousPatternPrefix ctx) :
    Core.Routing.ResidualStage .ct9 (HomogeneousPatternLedger ctx verified.1) :=
  verified.2

theorem exists_verifiedHomogeneousPatternPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedHomogeneousPatternPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedCoupledClassOverloadPrefix object baseline avoids
  exact ⟨ctx, verifiedHomogeneousPatternPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
