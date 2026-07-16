import Erdos64EG.SurplusScaleSplit
import Erdos64EG.P13MultiScaleCurvatureCertificateAudit
import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

abbrev P13BarrierCandidate := Fin 14 × Fin 14

def P13BarrierAccepted (candidate : P13BarrierCandidate) : Prop :=
  candidate.1.1 + candidate.2.1 ≤ 12

def p13BarrierAcceptedDecidable (candidate : P13BarrierCandidate) :
    Decidable (P13BarrierAccepted candidate) := by
  unfold P13BarrierAccepted
  infer_instance

def p13BarrierClassification :
    CT10.ExhaustiveClassification.Profile P13BarrierCandidate where
  candidates := inferInstance
  Accepts := P13BarrierAccepted
  acceptsDecidable := p13BarrierAcceptedDecidable

abbrev P13BarrierIndex := p13BarrierClassification.Class

def P13BarrierIndex.leftLength (index : P13BarrierIndex) : Nat :=
  index.1.1.1 + 1

def P13BarrierIndex.rightLength (index : P13BarrierIndex) : Nat :=
  index.1.2.1 + 1

theorem p13BarrierIndex_positive (index : P13BarrierIndex) :
    1 ≤ index.leftLength ∧ 1 ≤ index.rightLength := by
  simp [P13BarrierIndex.leftLength, P13BarrierIndex.rightLength]

theorem p13BarrierIndex_sum_le_fourteen (index : P13BarrierIndex) :
    index.leftLength + index.rightLength ≤ 14 := by
  unfold P13BarrierIndex.leftLength P13BarrierIndex.rightLength
  have accepted := index.property
  change index.1.1.1 + index.1.2.1 ≤ 12 at accepted
  omega

theorem p13BarrierIndex_lt_fifteen (index : P13BarrierIndex) :
    index.leftLength < 15 ∧ index.rightLength < 15 := by
  have positive := p13BarrierIndex_positive index
  have sumBound := p13BarrierIndex_sum_le_fourteen index
  omega

theorem p13Barrier_candidate_count :
    p13BarrierClassification.candidateCount = 196 := by
  native_decide

theorem p13Barrier_class_count :
    p13BarrierClassification.classCount = 91 := by
  native_decide

def p13MultiScaleCompatibilityRow (length : Nat) (source : Fin 399) :
    BitVec 399 :=
  P13MultiScaleCurvatureCertificate.row length source

def p13MultiScaleBarrierProfile :
    Core.FiniteBitRelationBarrier.Profile 399 :=
  P13MultiScaleCurvatureCertificate.profile

theorem p13MultiScaleCompatibilityRow_semantic
    (length : Nat) (length_lt : length < 15) (source target : Fin 399) :
    (p13MultiScaleCompatibilityRow length source).getLsb target = true ↔
      p13C length (p13CurvatureLabel source)
        (p13CurvatureLabel target) = 1 := by
  rw [show p13MultiScaleCompatibilityRow length source =
      P13MultiScaleCurvatureCertificate.row length source by rfl,
    p13MultiScaleRows_codeAudit ⟨length, length_lt⟩ source target]
  simp only [decide_eq_true_eq, p13C_eq_one_iff, p13CurvatureLabel]
  exact (p13CodeCompatibleSparse_iff length length_lt _ _).trans <|
    (p13CodeCompatibleBits_iff length length_lt _ _).trans <|
    (p13CodeCompatibleFast_iff length _ _).trans
    (p13CodeCompatible_iff length _ _)

def p13BarrierSafeCount (index : P13BarrierIndex) : Nat :=
  P13MultiScaleCurvatureCertificate.safeCount
    index.leftLength index.rightLength

def p13BarrierFlatCount (index : P13BarrierIndex) : Nat :=
  P13MultiScaleCurvatureCertificate.flatCount
    index.leftLength index.rightLength

def p13BarrierObstructedCount (index : P13BarrierIndex) : Nat :=
  p13BarrierSafeCount index - p13BarrierFlatCount index

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

def p13BarrierSafeProduct : Nat :=
  (p13BarrierClassification.classes.orderedValues.map
    p13BarrierSafeCount).prod

def p13BarrierFlatProduct : Nat :=
  (p13BarrierClassification.classes.orderedValues.map
    p13BarrierFlatCount).prod

private theorem p13Barrier_computation :
    p13BarrierClassification.classes.orderedValues.all (fun index =>
      decide (0 < p13BarrierFlatCount index ∧
        p13BarrierFlatCount index ≤ p13BarrierSafeCount index)) = true ∧
    2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct ∧
    P13MultiScaleCurvatureCertificate.safeCount 1 1 = 543958 ∧
      P13MultiScaleCurvatureCertificate.safeCount 1 1 -
        P13MultiScaleCurvatureCertificate.flatCount 1 1 = 432672 ∧
      P13MultiScaleCurvatureCertificate.flatCount 1 1 = 111286 := by
  native_decide

theorem p13Barrier_counts_wellFormed :
    ∀ index : P13BarrierIndex,
      0 < p13BarrierFlatCount index ∧
        p13BarrierFlatCount index ≤ p13BarrierSafeCount index := by
  intro index
  have checked := (List.all_eq_true.mp p13Barrier_computation.1) index
    (p13BarrierClassification.classes.mem_orderedValues index)
  simpa only [decide_eq_true_eq, p13BarrierFlatCount, p13BarrierSafeCount]
    using checked

theorem p13Barrier_partition (index : P13BarrierIndex) :
    p13BarrierObstructedCount index + p13BarrierFlatCount index =
      p13BarrierSafeCount index := by
  exact Nat.sub_add_cancel (p13Barrier_counts_wellFormed index).2

theorem p13MultiScaleBarrier_more_than_118_bits :
    2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct :=
  p13Barrier_computation.2.1

theorem p13Barrier_one_one_counts :
    let index : P13BarrierIndex :=
      ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by
        change 0 + 0 ≤ 12
        decide⟩
    p13BarrierSafeCount index = 543958 ∧
      p13BarrierObstructedCount index = 432672 ∧
      p13BarrierFlatCount index = 111286 :=
  p13Barrier_computation.2.2

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

def p13MultiScaleCheckCount : Nat :=
  p13BarrierClassification.checks + 91 * (399 + 399 ^ 2)

theorem p13MultiScaleCheckCount_quadratic :
    p13MultiScaleCheckCount ≤ 92 * (399 + 1) ^ 2 := by
  native_decide

structure VerifiedP13MultiScaleCurvaturePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  previous : BoundedSurplusScaleResidual ctx
  stage : p13BarrierClassification.VerifiedStage ctx.toBranchContext
  barrierCount : p13BarrierClassification.classCount = 91
  semantic : ∀ length, length < 15 → ∀ source target,
    (p13MultiScaleCompatibilityRow length source).getLsb target = true ↔
      p13C length (p13CurvatureLabel source)
        (p13CurvatureLabel target) = 1
  wellFormed : ∀ index : P13BarrierIndex,
    0 < p13BarrierFlatCount index ∧
      p13BarrierFlatCount index ≤ p13BarrierSafeCount index
  safeCountAudit : ∀ index : P13BarrierIndex,
    p13BarrierSafeCount index = p13MultiScaleBarrierProfile.safeCount
      index.leftLength index.rightLength
  flatCountAudit : ∀ index : P13BarrierIndex,
    p13BarrierFlatCount index = p13MultiScaleBarrierProfile.flatCount
      index.leftLength index.rightLength
  rateFloor : 2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct
  oneOneCounts :
    let index : P13BarrierIndex :=
      ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by
        change 0 + 0 ≤ 12
        decide⟩
    p13BarrierSafeCount index = 543958 ∧
      p13BarrierObstructedCount index = 432672 ∧
      p13BarrierFlatCount index = 111286
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
  semantic := p13MultiScaleCompatibilityRow_semantic
  wellFormed := p13Barrier_counts_wellFormed
  safeCountAudit := p13BarrierSafeCount_audit
  flatCountAudit := p13BarrierFlatCount_audit
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

end Erdos64EG.Internal
