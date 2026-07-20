import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Batteries.Data.BitVec.Lemmas
import StructuralExhaustion.Core.ChunkedFiniteCount

namespace StructuralExhaustion.Core.FiniteBitRelationBarrier

/-!
# Finite relation-barrier counts

This module owns the integer arithmetic behind a finite two-leg relation
barrier.  A row at length `s` records the labels compatible with one source
label.  For lengths `a` and `b`, `safeCount` counts triples whose two legs are
compatible, while `flatCount` additionally requires the composed `a+b` leg.

The implementation uses bit-row intersections.  It does not enumerate a
family of ambient objects or a Boolean state cube.
-/

/-- A length-indexed family of Boolean relation matrices on `size` labels. -/
structure Profile (size : Nat) where
  row : Nat → Fin size → BitVec size

namespace Profile

variable {size : Nat} (profile : Profile size)

/-- Number of compatible two-leg triples, summed by their middle label. -/
def safeCount (leftLength rightLength : Nat) : Nat :=
  ∑ middle : Fin size,
    (profile.row leftLength middle).cpop.toNat *
      (profile.row rightLength middle).cpop.toNat

/-! A fixed-width evaluator for the same finite sum.  The equality theorem
below is algebraic; applications use it only to change the reduction shape
of a fixed local table. -/

def safeCountChunked (width leftLength rightLength : Nat) : Nat :=
  let value : Fin size → Nat := fun middle =>
    (profile.row leftLength middle).cpop.toNat *
      (profile.row rightLength middle).cpop.toNat
  (∑ chunk ∈ Finset.range (size / width),
      ChunkedFiniteCount.intervalSum
        (ChunkedFiniteCount.finZeroExtension value)
        (chunk * width) width) +
    ChunkedFiniteCount.intervalSum
      (ChunkedFiniteCount.finZeroExtension value)
      ((size / width) * width) (size % width)

theorem safeCount_eq_safeCountChunked (width leftLength rightLength : Nat) :
    profile.safeCount leftLength rightLength =
      profile.safeCountChunked width leftLength rightLength := by
  unfold safeCount safeCountChunked
  exact ChunkedFiniteCount.finSum_eq_chunkIntervals_add_tail
    (fun middle : Fin size =>
      (profile.row leftLength middle).cpop.toNat *
        (profile.row rightLength middle).cpop.toNat) width

/-- Number of two-leg triples whose composed leg is also compatible. -/
def flatCount (leftLength rightLength : Nat) : Nat :=
  ∑ source : Fin size, ∑ middle : Fin size,
    if (profile.row leftLength source).getLsb middle then
      (((profile.row rightLength middle) &&&
        (profile.row (leftLength + rightLength) source)).cpop).toNat
    else 0

/-- The complementary, composition-obstructed triple count. -/
def obstructedCount (leftLength rightLength : Nat) : Nat :=
  profile.safeCount leftLength rightLength -
    profile.flatCount leftLength rightLength

theorem obstructed_add_flat
    (leftLength rightLength : Nat)
    (flat_le : profile.flatCount leftLength rightLength ≤
      profile.safeCount leftLength rightLength) :
    profile.obstructedCount leftLength rightLength +
        profile.flatCount leftLength rightLength =
      profile.safeCount leftLength rightLength := by
  exact Nat.sub_add_cancel flat_le

/-- Primitive bit operations used by one barrier count. -/
def checks (_leftLength _rightLength : Nat) : Nat :=
  let _relation := profile.row
  size + size ^ 2

theorem checks_quadratic (leftLength rightLength : Nat) :
    profile.checks leftLength rightLength ≤ 2 * (size + 1) ^ 2 := by
  simp only [checks]
  nlinarith [Nat.zero_le size]

end Profile

/-- Pack one decidable relation row into the same compact representation used
by the barrier counters.  Applications can audit a stored row with one
`BitVec` equality instead of reifying one theorem per matrix entry. -/
def semanticRow {size : Nat}
    (relation : Fin size → Fin size → Bool) (source : Fin size) : BitVec size :=
  BitVec.ofFnLE (relation source)

@[simp] theorem semanticRow_getLsb {size : Nat}
    (relation : Fin size → Fin size → Bool) (source target : Fin size) :
    (semanticRow relation source).getLsb target = relation source target := by
  exact BitVec.getLsb_ofFnLE _ _

/-! ## Feature-column realization

Many finite relations are determined by a small feature mask even when their
carrier has hundreds of elements.  The following constructor forms a row by
OR-ing exactly the columns selected by a mask and then complementing the
result.  Its cost is linear in `featureCount`, rather than quadratic in the
carrier size. -/

/-- OR the selected feature columns from an explicit local schedule. -/
def selectedFeatureUnionList {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size) (mask : BitVec featureCount) :
    List (Fin featureCount) → BitVec size
  | [] => 0
  | feature :: rest =>
      if mask.getLsb feature then
        columns feature ||| selectedFeatureUnionList columns mask rest
      else
        selectedFeatureUnionList columns mask rest

theorem selectedFeatureUnionList_getLsb {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size) (mask : BitVec featureCount)
    (features : List (Fin featureCount)) (target : Fin size) :
    (selectedFeatureUnionList columns mask features).getLsb target =
      features.any (fun feature =>
        mask.getLsb feature && (columns feature).getLsb target) := by
  induction features with
  | nil => simp [selectedFeatureUnionList]
  | cons feature rest ih =>
      simp only [selectedFeatureUnionList, List.any_cons]
      split <;> simp_all

/-- OR all feature columns selected by `mask`. -/
def selectedFeatureUnion {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size) (mask : BitVec featureCount) :
    BitVec size :=
  selectedFeatureUnionList columns mask (List.finRange featureCount)

theorem selectedFeatureUnion_getLsb {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size) (mask : BitVec featureCount)
    (target : Fin size) :
    (selectedFeatureUnion columns mask).getLsb target =
      (List.finRange featureCount).any (fun feature =>
        mask.getLsb feature && (columns feature).getLsb target) := by
  exact selectedFeatureUnionList_getLsb columns mask _ target

/-- The carrier row whose targets avoid every feature selected by `mask`. -/
def featureAvoidanceRow {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size) (mask : BitVec featureCount) :
    BitVec size :=
  ~~~(selectedFeatureUnion columns mask)

theorem featureAvoidanceRow_getLsb {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size) (mask : BitVec featureCount)
    (target : Fin size) :
    (featureAvoidanceRow columns mask).getLsb target =
      !(List.finRange featureCount).any (fun feature =>
        mask.getLsb feature && (columns feature).getLsb target) := by
  change (~~~(selectedFeatureUnion columns mask)).getLsb target = _
  rw [show (~~~(selectedFeatureUnion columns mask)).getLsb target =
      !(selectedFeatureUnion columns mask).getLsb target by simp]
  rw [selectedFeatureUnion_getLsb]

theorem and_eq_zero_iff_no_selected {featureCount : Nat}
    (mask target : BitVec featureCount) :
    mask &&& target = 0#featureCount ↔
      ∀ feature : Fin featureCount,
        mask.getLsb feature = true → target.getLsb feature = false := by
  constructor
  · intro zero feature selected
    have bit := congrArg
      (fun bits : BitVec featureCount => bits.getLsb feature) zero
    have implication : mask.getLsb feature = true →
        target.getLsb feature = false := by
      simpa using bit
    exact implication selected
  · intro disjoint
    apply BitVec.eq_of_getElem_eq
    intro index index_lt
    let feature : Fin featureCount := ⟨index, index_lt⟩
    rw [BitVec.getElem_and, BitVec.getElem_zero]
    change (mask.getLsb feature && target.getLsb feature) = false
    cases selected : mask.getLsb feature
    · simp
    · have absent := disjoint feature selected
      simpa [BitVec.getLsb_eq_getElem] using absent

/-- Moving one fixed-width bit mask left is adjoint, for disjointness, to
moving the tested target right.  The proof is coordinate-local and performs
no finite-carrier enumeration. -/
theorem shiftLeft_and_eq_zero_iff_and_ushiftRight_eq_zero
    {width : Nat} (left right : BitVec width) (shift : Nat) :
    (left <<< shift) &&& right = 0#width ↔
      left &&& (right >>> shift) = 0#width := by
  rw [BitVec.zero_iff_eq_false, BitVec.zero_iff_eq_false]
  constructor
  · intro zero index
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
    by_cases inBounds : shift + index < width
    · have shiftedNotLow : ¬ shift + index < shift := by omega
      have bit := zero (shift + index)
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] at bit
      simpa [inBounds, shiftedNotLow] using bit
    · have rightFalse : right.getLsbD (shift + index) = false :=
        BitVec.getLsbD_of_ge right (shift + index) (by omega)
      simp [rightFalse]
  · intro zero index
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    by_cases inBounds : index < width
    · by_cases aboveShift : shift ≤ index
      · have notLow : ¬ index < shift := by omega
        have bit := zero (index - shift)
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight] at bit
        have shiftedIndex : shift + (index - shift) = index := by omega
        simpa [inBounds, notLow, shiftedIndex] using bit
      · have low : index < shift := by omega
        simp [inBounds, low]
    · simp [inBounds]

/-- Bitwise union of a proof-selected finite list of masks. -/
def maskUnion {width : Nat} : List (BitVec width) → BitVec width
  | [] => 0
  | mask :: rest => mask ||| maskUnion rest

/-- A target avoids a finite union exactly when it avoids every constituent
mask. -/
theorem maskUnion_and_eq_zero_iff {width : Nat}
    (masks : List (BitVec width)) (target : BitVec width) :
    maskUnion masks &&& target = 0#width ↔
      ∀ mask ∈ masks, mask &&& target = 0#width := by
  induction masks with
  | nil => simp [maskUnion]
  | cons mask rest ih =>
      rw [maskUnion, BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff, ih]
      simp only [List.mem_cons, forall_eq_or_imp]

/-! ## Shallow interval audits -/

/-- Embed one small numeric audit interval in its complete finite carrier. -/
def intervalIndex {total : Nat} (start width : Nat)
    (fits : start + width ≤ total) (offset : Fin width) : Fin total :=
  ⟨start + offset.1, by omega⟩

@[simp] theorem intervalIndex_val {total : Nat} (start width : Nat)
    (fits : start + width ≤ total) (offset : Fin width) :
    (intervalIndex start width fits offset).1 = start + offset.1 :=
  rfl

/-- Retrieve an arbitrary member of an already checked small interval.  This
lets applications combine independent kernel decisions on `Fin width`
without asking the kernel to normalize the entire carrier at once. -/
theorem intervalProof_at {total : Nat} {P : Fin total → Prop}
    {start width : Nat} (fits : start + width ≤ total)
    (checked : ∀ offset : Fin width, P (intervalIndex start width fits offset))
    (source : Fin total) (lower : start ≤ source.1)
    (upper : source.1 < start + width) : P source := by
  let offset : Fin width := ⟨source.1 - start, by omega⟩
  have exactIndex : intervalIndex start width fits offset = source := by
    apply Fin.ext
    simp [offset]
    omega
  simpa [exactIndex] using checked offset

/-- Equality-specialized retrieval from one already checked small interval.

Keeping the two indexed families explicit avoids asking elaboration to recover
an arbitrary higher-order predicate from an equality shard. Applications can
partially apply this theorem once to their two families, then reuse the
resulting retriever across every shallow interval. -/
theorem intervalEquality_at {total : Nat} {value : Type*}
    (left right : Fin total → value) (start width : Nat)
    (fits : start + width ≤ total)
    (checked : ∀ offset : Fin width,
      left (intervalIndex start width fits offset) =
        right (intervalIndex start width fits offset))
    (source : Fin total) (lower : start ≤ source.1)
    (upper : source.1 < start + width) : left source = right source :=
  intervalProof_at (P := fun index ↦ left index = right index)
    fits checked source lower upper

/-- Once columns are certified pointwise, the compact row tests exactly
whether the target code is disjoint from the selected feature mask. -/
theorem featureAvoidanceRow_getLsb_eq_decide_and_zero
    {featureCount size : Nat}
    (columns : Fin featureCount → BitVec size)
    (code : Fin size → BitVec featureCount)
    (columnsExact : ∀ feature target,
      (columns feature).getLsb target = (code target).getLsb feature)
    (mask : BitVec featureCount) (target : Fin size) :
    (featureAvoidanceRow columns mask).getLsb target =
      decide (mask &&& code target = 0#featureCount) := by
  apply Bool.eq_iff_iff.mpr
  rw [featureAvoidanceRow_getLsb, Bool.not_eq_true_eq_eq_false,
    decide_eq_true_eq, and_eq_zero_iff_no_selected]
  simp only [List.any_eq_false, List.mem_finRange, Bool.not_eq_true,
    Bool.and_eq_false_imp, columnsExact]
  constructor
  · intro noHit feature selected
    exact noHit feature trivial selected
  · intro noHit feature _ selected
    exact noHit feature selected

/-- Exact semantic ownership for every row of a finite relation profile.

The certificate deliberately stores whole-row equalities.  This keeps fixed
table validation compact while its projection still supplies the pointwise
entry theorem expected by semantic consumers. -/
structure SemanticCertificate {size : Nat} (profile : Profile size)
    (Length : Type*) (lengthValue : Length → Nat)
    (relation : Length → Fin size → Fin size → Bool) : Prop where
  rowExact : ∀ length source,
    profile.row (lengthValue length) source = semanticRow (relation length) source

namespace SemanticCertificate

variable {size : Nat} {profile : Profile size} {Length : Type*}
  {lengthValue : Length → Nat}
  {relation : Length → Fin size → Fin size → Bool}

theorem getLsb_eq
    (certificate : SemanticCertificate profile Length lengthValue relation)
    (length : Length) (source target : Fin size) :
    (profile.row (lengthValue length) source).getLsb target =
      relation length source target := by
  rw [certificate.rowExact length source]
  exact semanticRow_getLsb _ _ _

end SemanticCertificate

/-- Exact ownership of cached safe/flat counts by a finite barrier profile.
The index type is the proof-selected local schedule; this abstraction performs
no ambient enumeration. -/
structure CountCertificate {size : Nat} (profile : Profile size)
    (Index : Type*) where
  leftLength : Index → Nat
  rightLength : Index → Nat
  storedSafe : Index → Nat
  storedFlat : Index → Nat
  safeExact : ∀ index,
    storedSafe index = profile.safeCount (leftLength index) (rightLength index)
  flatExact : ∀ index,
    storedFlat index = profile.flatCount (leftLength index) (rightLength index)

/-- One reusable owner for the semantic relation rows and all cached counts on
the proof-selected local index schedule. -/
structure CertifiedTable {size : Nat} (profile : Profile size)
    (Length : Type*) (lengthValue : Length → Nat)
    (relation : Length → Fin size → Fin size → Bool)
    (Index : Type*) where
  semantic : SemanticCertificate profile Length lengthValue relation
  counts : CountCertificate profile Index

end StructuralExhaustion.Core.FiniteBitRelationBarrier
