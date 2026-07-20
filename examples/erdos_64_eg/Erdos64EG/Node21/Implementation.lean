import Erdos64EG.Shared.SurplusScaleSplit
import Erdos64EG.Node21.API
import Erdos64EG.Node21.Certificates
import StructuralExhaustion.Core.FiniteBitRelationBarrier
import StructuralExhaustion.Core.FiniteTriangle

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

set_option maxRecDepth 10000

universe u

/-!
# CT10: the complete multi-scale P13 curvature table

This is the missing finite part of manuscript node `[21]`. CT10 classifies
the 196 ordered pairs of positive path lengths and retains exactly the 91
pairs `(a,b)` with `a+b ≤ 14`. A reusable bit-relation profile then computes
the safe and composition-flat triple counts for each accepted pair.

The downstream quantitative certificate is the integer inequality
`2^118 * product(flat counts) < product(safe counts)`. It is the exact,
rounding-free form of the statement that the sum of the 91 finite barrier
rates is greater than 118 bits. No logarithm, floating-point value, graph
family, or Boolean state cube is evaluated here.
-/

theorem p13BarrierIndex_positive (index : P13BarrierIndex) :
    1 ≤ index.leftLength ∧ 1 ≤ index.rightLength := by
  simp [P13BarrierIndex.leftLength, P13BarrierIndex.rightLength]

theorem p13BarrierIndex_sum_le_fourteen (index : P13BarrierIndex) :
    index.leftLength + index.rightLength ≤ 14 := by
  unfold P13BarrierIndex.leftLength P13BarrierIndex.rightLength
  have accepted := index.property
  change index.1.1.1 + index.1.2.1 < 13 at accepted
  omega

theorem p13BarrierIndex_lt_fifteen (index : P13BarrierIndex) :
    index.leftLength < 15 ∧ index.rightLength < 15 := by
  have positive := p13BarrierIndex_positive index
  have sumBound := p13BarrierIndex_sum_le_fourteen index
  omega

theorem p13Barrier_candidate_count :
    p13BarrierClassification.candidateCount = 196 := by
  rw [CT10.ExhaustiveClassification.Profile.candidateCount]
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_prod]
  norm_num

theorem p13Barrier_class_count :
    p13BarrierClassification.classCount = 91 := by
  rw [CT10.ExhaustiveClassification.Profile.classCount]
  rw [← Core.Enumeration.natCard_eq p13BarrierClassification.classes]
  change Nat.card (Core.FiniteTriangle.Pair 13) = 91
  rw [Core.FiniteTriangle.natCard_eq_sum]
  norm_num [Fin.sum_univ_succ]

def p13MultiScaleCompatibilityRow (length : Nat) (source : Fin 399) :
    BitVec 399 :=
  P13MultiScaleCurvatureCertificate.row length source

theorem p13MultiScaleCompatibilityRow_semantic
    (length : Nat) (length_lt : length < 15) (source target : Fin 399) :
    (p13MultiScaleCompatibilityRow length source).getLsb target = true ↔
      p13C length (p13CurvatureLabel source)
        (p13CurvatureLabel target) = 1 := by
  rw [show p13MultiScaleCompatibilityRow length source =
      P13MultiScaleCurvatureCertificate.row length source by rfl,
    p13MultiScaleRows_codeAudit ⟨length, length_lt⟩ source target]
  simp only [P13MultiScaleCurvatureCertificate.semanticRelation,
    p13FeatureSemanticRelation, decide_eq_true_eq, p13C_eq_one_iff,
    p13CurvatureLabel]
  exact (p13CodeCompatibleSparse_iff length length_lt _ _).trans <|
    (p13CodeCompatibleBits_iff length length_lt _ _).trans <|
    (p13CodeCompatibleFast_iff length _ _).trans
    (p13CodeCompatible_iff length _ _)

theorem p13BarrierSafeCount_audit (index : P13BarrierIndex) :
    p13BarrierSafeCount index = p13MultiScaleBarrierProfile.safeCount
      index.leftLength index.rightLength := by
  have audited := p13MultiScaleSafeCounts_audit
    ⟨index.leftLength, (p13BarrierIndex_lt_fifteen index).1⟩
    ⟨index.rightLength, (p13BarrierIndex_lt_fifteen index).2⟩
  rw [if_pos ⟨(p13BarrierIndex_positive index).1,
    (p13BarrierIndex_positive index).2,
    p13BarrierIndex_sum_le_fourteen index⟩] at audited
  exact audited

theorem p13BarrierFlatCount_audit (index : P13BarrierIndex) :
    p13BarrierFlatCount index = p13MultiScaleBarrierProfile.flatCount
      index.leftLength index.rightLength := by
  have audited := p13MultiScaleFlatCounts_audit
    ⟨index.leftLength, (p13BarrierIndex_lt_fifteen index).1⟩
    ⟨index.rightLength, (p13BarrierIndex_lt_fifteen index).2⟩
  rw [if_pos ⟨(p13BarrierIndex_positive index).1,
    (p13BarrierIndex_positive index).2,
    p13BarrierIndex_sum_le_fourteen index⟩] at audited
  exact audited

def p13MultiScaleCountCertificate :
    Core.FiniteBitRelationBarrier.CountCertificate
      p13MultiScaleBarrierProfile P13BarrierIndex where
  leftLength := P13BarrierIndex.leftLength
  rightLength := P13BarrierIndex.rightLength
  storedSafe := p13BarrierSafeCount
  storedFlat := p13BarrierFlatCount
  safeExact := p13BarrierSafeCount_audit
  flatExact := p13BarrierFlatCount_audit

def p13MultiScaleCertifiedTable :
    Core.FiniteBitRelationBarrier.CertifiedTable
      p13MultiScaleBarrierProfile
      (Fin 15) (fun length => length.1)
      (fun length => P13MultiScaleCurvatureCertificate.semanticRelation length.1)
      P13BarrierIndex where
  semantic := p13MultiScaleSemanticCertificate
  counts := p13MultiScaleCountCertificate

private theorem p13Barrier_wellFormed_computation :
    p13BarrierClassification.classes.orderedValues.all (fun index =>
      decide (0 < p13BarrierFlatCount index ∧
        p13BarrierFlatCount index ≤ p13BarrierSafeCount index)) = true := by
  decide

private theorem p13Barrier_rate_computation :
    2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct := by
  decide

private theorem p13Barrier_oneOne_computation :
    P13MultiScaleCurvatureCertificate.safeCount 1 1 = 543958 ∧
      P13MultiScaleCurvatureCertificate.safeCount 1 1 -
        P13MultiScaleCurvatureCertificate.flatCount 1 1 = 432672 ∧
      P13MultiScaleCurvatureCertificate.flatCount 1 1 = 111286 := by
  decide

theorem p13Barrier_counts_wellFormed :
    ∀ index : P13BarrierIndex,
      0 < p13BarrierFlatCount index ∧
        p13BarrierFlatCount index ≤ p13BarrierSafeCount index := by
  intro index
  have checked := (List.all_eq_true.mp p13Barrier_wellFormed_computation) index
    (p13BarrierClassification.classes.mem_orderedValues index)
  simpa only [decide_eq_true_eq, p13BarrierFlatCount, p13BarrierSafeCount]
    using checked

theorem p13Barrier_partition (index : P13BarrierIndex) :
    p13BarrierObstructedCount index + p13BarrierFlatCount index =
      p13BarrierSafeCount index := by
  exact Nat.sub_add_cancel (p13Barrier_counts_wellFormed index).2

theorem p13MultiScaleBarrier_more_than_118_bits :
    2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct :=
  p13Barrier_rate_computation

theorem p13Barrier_one_one_counts :
    P13MultiScaleCurvatureCertificate.safeCount 1 1 = 543958 ∧
      P13MultiScaleCurvatureCertificate.safeCount 1 1 -
          P13MultiScaleCurvatureCertificate.flatCount 1 1 = 432672 ∧
      P13MultiScaleCurvatureCertificate.flatCount 1 1 = 111286 :=
  p13Barrier_oneOne_computation

noncomputable def p13BarrierStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13BarrierClassification.VerifiedStage ctx.toBranchContext :=
  p13BarrierClassification.verifiedStage ctx.toBranchContext

theorem p13BarrierStage_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BarrierClassification.run ctx.toBranchContext).terminal = .exhaustive :=
  (p13BarrierStage ctx).terminal

theorem p13BarrierStage_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13BarrierClassification.run ctx.toBranchContext).trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  (p13BarrierStage ctx).trace

theorem p13MultiScaleCheckCount_quadratic :
    p13MultiScaleCheckCount ≤ 92 * (399 + 1) ^ 2 := by
  have classificationChecks : p13BarrierClassification.checks = 8568 := by
    rw [CT10.ExhaustiveClassification.Profile.checks,
      p13Barrier_candidate_count, p13Barrier_class_count]
    norm_num
  calc
    p13MultiScaleCheckCount =
        p13BarrierClassification.checks + 91 * (399 + 399 ^ 2) := rfl
    _ = 8568 + 91 * (399 + 399 ^ 2) := by rw [classificationChecks]
    _ ≤ 92 * (399 + 1) ^ 2 := by norm_num

noncomputable def node21MultiScaleCurvature {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node19Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node21Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueDependentDecisionNo
    fun _residual node18 bounded =>
      {
        stage := p13BarrierStage (Node21Context node18)
        barrierCount := p13Barrier_class_count
        certificate := p13MultiScaleCertifiedTable
        wellFormed := p13Barrier_counts_wellFormed
        rateFloor := p13MultiScaleBarrier_more_than_118_bits
        oneOneCounts := p13Barrier_one_one_counts
        terminal := p13BarrierStage_terminal (Node21Context node18)
        trace := p13BarrierStage_trace (Node21Context node18)
        polynomial := p13MultiScaleCheckCount_quadratic
        nearCubicBudget := bounded
      }

noncomputable def runInitialThroughNode21 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode19 residual).mapYesStage node21MultiScaleCurvature

structure VerifiedP13MultiScaleCurvaturePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  previous : BoundedSurplusScaleResidual ctx
  stage : p13BarrierClassification.VerifiedStage ctx.toBranchContext
  barrierCount : p13BarrierClassification.classCount = 91
  certificate : Core.FiniteBitRelationBarrier.CertifiedTable
    p13MultiScaleBarrierProfile
    (Fin 15) (fun length => length.1)
    (fun length => P13MultiScaleCurvatureCertificate.semanticRelation length.1)
    P13BarrierIndex
  wellFormed : ∀ index : P13BarrierIndex,
    0 < p13BarrierFlatCount index ∧
      p13BarrierFlatCount index ≤ p13BarrierSafeCount index
  rateFloor : 2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct
  oneOneCounts :
    P13MultiScaleCurvatureCertificate.safeCount 1 1 = 543958 ∧
      P13MultiScaleCurvatureCertificate.safeCount 1 1 -
          P13MultiScaleCurvatureCertificate.flatCount 1 1 = 432672 ∧
      P13MultiScaleCurvatureCertificate.flatCount 1 1 = 111286
  terminal :
    (p13BarrierClassification.run ctx.toBranchContext).terminal = .exhaustive
  trace : (p13BarrierClassification.run ctx.toBranchContext).trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal]
  polynomial : p13MultiScaleCheckCount ≤ 92 * (399 + 1) ^ 2

noncomputable def verifiedP13MultiScaleCurvaturePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : BoundedSurplusScaleResidual ctx) :
    VerifiedP13MultiScaleCurvaturePrefix ctx where
  previous := previous
  stage := p13BarrierStage ctx
  barrierCount := p13Barrier_class_count
  certificate := p13MultiScaleCertifiedTable
  wellFormed := p13Barrier_counts_wellFormed
  rateFloor := p13MultiScaleBarrier_more_than_118_bits
  oneOneCounts := p13Barrier_one_one_counts
  terminal := p13BarrierStage_terminal ctx
  trace := p13BarrierStage_trace ctx
  polynomial := p13MultiScaleCheckCount_quadratic

/-- The exact node-[19] route with its bounded constructor discharged by the
complete node-[21] CT10 certificate.  The strict constructor is preserved
unchanged for the already implemented Part-X branch. -/
inductive SurplusScaleCurvatureRoute
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
  | sparsePressure : SparsePressureEntryResidual ctx →
      SurplusScaleCurvatureRoute ctx
  | curvature : VerifiedP13MultiScaleCurvaturePrefix ctx →
      SurplusScaleCurvatureRoute ctx

noncomputable def routeSurplusScaleThroughCurvature
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx)
    (windowSize remainderSize primitiveSize : Nat) :
    SurplusScaleCurvatureRoute ctx :=
  match routeSurplusScale ctx previous windowSize remainderSize primitiveSize with
  | .sparsePressure residual => .sparsePressure residual
  | .bounded residual =>
      .curvature (verifiedP13MultiScaleCurvaturePrefix ctx residual)

theorem routeSurplusScaleThroughCurvature_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSurplusScaleSplitPrefix ctx)
    (windowSize remainderSize primitiveSize : Nat) :
    (∃ residual : SparsePressureEntryResidual ctx,
        routeSurplusScaleThroughCurvature ctx previous windowSize remainderSize
          primitiveSize = .sparsePressure residual) ∨
      (∃ certificate : VerifiedP13MultiScaleCurvaturePrefix ctx,
        routeSurplusScaleThroughCurvature ctx previous windowSize remainderSize
          primitiveSize = .curvature certificate) := by
  generalize routeEq :
    routeSurplusScale ctx previous windowSize remainderSize primitiveSize = route
  cases route with
  | sparsePressure residual =>
      exact Or.inl ⟨residual, by
        simp [routeSurplusScaleThroughCurvature, routeEq]⟩
  | bounded residual =>
      exact Or.inr ⟨verifiedP13MultiScaleCurvaturePrefix ctx residual, by
        simp [routeSurplusScaleThroughCurvature, routeEq]⟩

#print axioms node21MultiScaleCurvature
#print axioms runInitialThroughNode21

end Erdos64EG.Internal
