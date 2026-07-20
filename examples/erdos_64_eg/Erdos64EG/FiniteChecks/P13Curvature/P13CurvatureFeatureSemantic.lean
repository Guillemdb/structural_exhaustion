import Erdos64EG.FiniteChecks.P13MultiScaleCurvature.P13MultiScaleBitSemantic
import Erdos64EG.FiniteChecks.P13CurvatureFeatureColumns.P13CurvatureFeatureColumnAudit
import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace Erdos64EG.Internal

open StructuralExhaustion

/-!
# Feature-mask semantics for node [21]

For one source label and one connector length, compatibility forbids at most
thirteen target positions.  This file converts the sparse gap clauses into
that thirteen-bit mask and then lets the Core feature-column constructor
assemble the complete 399-target row.  No pair of carrier universes is ever
enumerated.
-/

/-- Target positions forbidden by one source gap. -/
def p13GapForbiddenMask (gap : Nat) (source : P13LabelCode) : P13LabelCode :=
  if gap = 0 then source
  else (source <<< gap) ||| (source >>> gap)

/-- The union of the masks selected by the manuscript's local sparse gap
schedule at one connector scale. -/
def p13ForbiddenMask (shift : Nat) (source : P13LabelCode) : P13LabelCode :=
  Core.FiniteBitRelationBarrier.maskUnion
    ((p13ForbiddenGaps shift).map fun gap =>
      p13GapForbiddenMask gap source)

theorem p13GapForbiddenMask_and_eq_zero_iff
    (gap : Nat) (source target : P13LabelCode) :
    p13GapForbiddenMask gap source &&& target = 0#13 ↔
      if gap = 0 then source &&& target = 0#13
      else source &&& (target >>> gap) = 0#13 ∧
        target &&& (source >>> gap) = 0#13 := by
  by_cases zero : gap = 0
  · subst gap
    simp [p13GapForbiddenMask]
  · simp only [p13GapForbiddenMask, if_neg zero,
      BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff]
    constructor
    · rintro ⟨forward, backward⟩
      exact ⟨
        (Core.FiniteBitRelationBarrier.shiftLeft_and_eq_zero_iff_and_ushiftRight_eq_zero
            source target gap).1 forward,
        by simpa [BitVec.and_comm] using backward⟩
    · rintro ⟨forward, backward⟩
      exact ⟨
        (Core.FiniteBitRelationBarrier.shiftLeft_and_eq_zero_iff_and_ushiftRight_eq_zero
            source target gap).2 forward,
        by simpa [BitVec.and_comm] using backward⟩

/-- The sparse manuscript relation is exactly disjointness from the local
thirteen-bit forbidden mask. -/
theorem p13CodeCompatibleSparse_iff_forbiddenMask
    (shift : Nat) (source target : P13LabelCode) :
    P13CodeCompatibleSparse shift source target ↔
      p13ForbiddenMask shift source &&& target = 0#13 := by
  unfold P13CodeCompatibleSparse p13ForbiddenMask
  rw [Core.FiniteBitRelationBarrier.maskUnion_and_eq_zero_iff]
  constructor
  · intro compatible mask maskMember
    rcases List.mem_map.mp maskMember with ⟨gap, gapMember, rfl⟩
    exact (p13GapForbiddenMask_and_eq_zero_iff gap source target).2
      (compatible gap gapMember)
  · intro avoids gap gapMember
    apply (p13GapForbiddenMask_and_eq_zero_iff gap source target).1
    exact avoids _ (List.mem_map.mpr ⟨gap, gapMember, rfl⟩)

/-- Compatibility row assembled from thirteen certified carrier-feature
columns. -/
def p13FeatureCompatibilityRow (shift : Nat) (source : Fin 399) : BitVec 399 :=
  Core.FiniteBitRelationBarrier.featureAvoidanceRow
    p13AscendingFeatureColumn
    (p13ForbiddenMask shift (p13AscendingCode source))

/-- Public Boolean relation on the shallow carrier. -/
def p13FeatureSemanticRelation
    (shift : Nat) (source target : Fin 399) : Bool :=
  @decide
    (P13CodeCompatibleSparse shift
      (p13AscendingCode source) (p13AscendingCode target))
    (p13CodeCompatibleSparseDecidable shift _ _)

def p13FeatureSemanticRow (shift : Nat) (source : Fin 399) : BitVec 399 :=
  Core.FiniteBitRelationBarrier.semanticRow
    (p13FeatureSemanticRelation shift) source

theorem p13FeatureCompatibilityRow_getLsb
    (shift : Nat) (source target : Fin 399) :
    (p13FeatureCompatibilityRow shift source).getLsb target =
      p13FeatureSemanticRelation shift source target := by
  rw [p13FeatureCompatibilityRow,
    Core.FiniteBitRelationBarrier.featureAvoidanceRow_getLsb_eq_decide_and_zero
        p13AscendingFeatureColumn p13AscendingCode
        p13AscendingFeatureColumn_exact]
  apply Bool.eq_iff_iff.mpr
  simp only [p13FeatureSemanticRelation, decide_eq_true_eq]
  exact (p13CodeCompatibleSparse_iff_forbiddenMask shift
    (p13AscendingCode source) (p13AscendingCode target)).symm

theorem p13FeatureCompatibilityRow_eq_semanticRow
    (shift : Nat) (source : Fin 399) :
    p13FeatureCompatibilityRow shift source =
      p13FeatureSemanticRow shift source := by
  apply BitVec.eq_of_getElem_eq
  intro index index_lt
  let target : Fin 399 := ⟨index, index_lt⟩
  change (p13FeatureCompatibilityRow shift source).getLsb target =
    (p13FeatureSemanticRow shift source).getLsb target
  rw [p13FeatureCompatibilityRow_getLsb]
  exact (Core.FiniteBitRelationBarrier.semanticRow_getLsb
    (p13FeatureSemanticRelation shift) source target).symm

end Erdos64EG.Internal
