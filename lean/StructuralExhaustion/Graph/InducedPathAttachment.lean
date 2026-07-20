import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.BitVec
import Mathlib.Tactic
import StructuralExhaustion.CT10.ExhaustiveClassification
import StructuralExhaustion.Graph.Cycle
import StructuralExhaustion.Graph.FiniteObject
import StructuralExhaustion.Graph.InducedPath

namespace StructuralExhaustion.Graph.InducedPathAttachment

open StructuralExhaustion

universe uVertex

/-!
# Finite attachment algebra around an induced path

The label of a vertex outside a labelled induced path is the finite set of
path positions adjacent to that vertex.  `Legal` records the cycle lengths
forbidden between two attachments.  `Compatible`, `C`, and `omegaTwo` are the
problem-independent finite relations used by path-label counting arguments.
-/

/-- A finite set of positions on a path with `order` vertices. -/
abbrev Label (order : Nat) := Finset (Fin order)

/-- Exact finite universe of all path-position labels. -/
@[implicit_reducible]
def labels (order : Nat) : FinEnum (Label order) := inferInstance

/-! ## Compact exact encoding of path-position labels -/

/-- One bit per path position. -/
abbrev LabelCode (order : Nat) := BitVec order

/-- Decode a compact label code to its selected path positions. -/
def decodeCode {order : Nat} (code : LabelCode order) : Label order :=
  Finset.univ.filter fun position => code.getLsb position

/-- Encode a path-position set with one bit per position. -/
def encodeLabel {order : Nat} (label : Label order) : LabelCode order :=
  BitVec.ofFnLE fun position => decide (position ∈ label)

/-- Exact equivalence between compact codes and path-position sets. -/
def labelCodeEquiv (order : Nat) : LabelCode order ≃ Label order where
  toFun := decodeCode
  invFun := encodeLabel
  left_inv := by
    intro code
    apply BitVec.eq_of_getElem_eq
    intro index index_lt
    simp [encodeLabel, decodeCode, BitVec.getElem_ofFnLE]
  right_inv := by
    intro label
    ext position
    simp [decodeCode, encodeLabel]

@[simp] theorem labelCodeEquiv_apply {order : Nat}
    (code : LabelCode order) :
    labelCodeEquiv order code = decodeCode code :=
  rfl

@[simp] theorem labelCodeEquiv_symm_apply {order : Nat}
    (label : Label order) :
    (labelCodeEquiv order).symm label = encodeLabel label :=
  rfl

/-- Sequential exact enumeration of the `2^order` compact label codes. -/
@[implicit_reducible]
def labelCodes (order : Nat) : FinEnum (LabelCode order) :=
  FinEnum.ofEquiv (Fin (2 ^ order))
    (BitVec.equivFin : BitVec order ≃+* Fin (2 ^ order)).toEquiv

/-- The compact path-label carrier has the expected symbolic cardinality. -/
theorem labelCodes_card (order : Nat) :
    @FinEnum.card (LabelCode order) (labelCodes order) = 2 ^ order :=
  by
    change FinEnum.card (Fin (2 ^ order)) = 2 ^ order
    exact FinEnum.card_fin

@[simp] theorem mem_decodeCode_iff {order : Nat}
    (code : LabelCode order) (position : Fin order) :
    position ∈ decodeCode code ↔ code.getLsb position = true := by
  simp [decodeCode]

/-- A code is nonzero exactly when it represents a nonempty attachment
label. -/
theorem decodeCode_nonempty_iff {order : Nat} (code : LabelCode order) :
    (decodeCode code).Nonempty ↔ code ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty]
  constructor
  · intro decodedNe codeZero
    subst code
    exact decodedNe (by ext position; simp [decodeCode])
  · intro codeNe decodedEmpty
    apply codeNe
    apply BitVec.eq_of_getElem_eq
    intro index index_lt
    have absent : (⟨index, index_lt⟩ : Fin order) ∉ decodeCode code := by
      simp [decodedEmpty]
    have bitFalse : code.getLsb ⟨index, index_lt⟩ = false := by
      simpa [decodeCode] using absent
    simpa [BitVec.getLsb_eq_getElem] using bitFalse

/-- A shifted bit intersection is zero exactly when the represented label
contains no ordered pair at that positive gap.  This is symbolic in the
code; it does not enumerate the `2^order` label universe. -/
theorem and_shift_eq_zero_iff_no_gap {order : Nat}
    (code : LabelCode order) (gap : Nat) (gapPositive : 0 < gap) :
    code &&& (code >>> gap) = 0 ↔
      ∀ left : Fin order, left ∈ decodeCode code →
        ∀ right : Fin order, right ∈ decodeCode code →
          left < right → right.1 - left.1 ≠ gap := by
  constructor
  · intro zero left leftMember right rightMember left_lt_right gapEq
    have rightEq : gap + left.1 = right.1 := by omega
    have bitEq := congrArg (fun bits : LabelCode order => bits[left.1]) zero
    have leftBit : code.getLsb left = true := by
      simpa [decodeCode] using leftMember
    have rightBit : code.getLsbD (gap + left.1) = true := by
      rw [rightEq, BitVec.getLsbD_eq_getElem right.isLt]
      simpa [decodeCode] using rightMember
    have leftElem : code[left.1] = true := by
      simpa [BitVec.getLsb_eq_getElem] using leftBit
    simp [BitVec.getElem_and, BitVec.getElem_ushiftRight,
      leftElem, rightBit] at bitEq
  · intro noGap
    apply BitVec.eq_of_getElem_eq
    intro index index_lt
    let left : Fin order := ⟨index, index_lt⟩
    by_cases leftMember : left ∈ decodeCode code
    · by_cases right_lt : gap + index < order
      · let right : Fin order := ⟨gap + index, right_lt⟩
        have rightNotMember : right ∉ decodeCode code := by
          intro rightMember
          have forbidden := noGap left leftMember right rightMember (by
            change index < gap + index
            omega)
          apply forbidden
          change (gap + index) - index = gap
          omega
        have leftBit : code.getLsb left = true := by
          simpa [decodeCode] using leftMember
        have rightBit : code.getLsbD (gap + index) = false := by
          rw [BitVec.getLsbD_eq_getElem right_lt]
          simpa [decodeCode, right] using rightNotMember
        simp [BitVec.getElem_and, BitVec.getElem_ushiftRight,
          rightBit]
      · have rightBit : code.getLsbD (gap + index) = false := by
          apply BitVec.getLsbD_of_ge
          omega
        simp [BitVec.getElem_and, BitVec.getElem_ushiftRight, rightBit]
    · have leftBit : code.getLsb left = false := by
        simpa [decodeCode] using leftMember
      have leftElem : code[index] = false := by
        simpa [left, BitVec.getLsb_eq_getElem] using leftBit
      simp [BitVec.getElem_and, BitVec.getElem_ushiftRight, leftElem]

/-- A shifted intersection of two codes is zero exactly when the decoded
labels contain no cross-label ordered pair at that positive gap.  This is the
two-label analogue of `and_shift_eq_zero_iff_no_gap` and supports compact
compatibility-matrix certificates. -/
theorem and_shift_cross_eq_zero_iff_no_gap {order : Nat}
    (leftCode rightCode : LabelCode order) (gap : Nat) (gapPositive : 0 < gap) :
    leftCode &&& (rightCode >>> gap) = 0 ↔
      ∀ left : Fin order, left ∈ decodeCode leftCode →
        ∀ right : Fin order, right ∈ decodeCode rightCode →
          left < right → right.1 - left.1 ≠ gap := by
  constructor
  · intro zero left leftMember right rightMember left_lt_right gapEq
    have rightEq : gap + left.1 = right.1 := by omega
    have bitEq := congrArg (fun bits : LabelCode order => bits[left.1]) zero
    have leftBit : leftCode.getLsb left = true := by
      simpa [decodeCode] using leftMember
    have rightBit : rightCode.getLsbD (gap + left.1) = true := by
      rw [rightEq, BitVec.getLsbD_eq_getElem right.isLt]
      simpa [decodeCode] using rightMember
    have leftElem : leftCode[left.1] = true := by
      simpa [BitVec.getLsb_eq_getElem] using leftBit
    simp [BitVec.getElem_and, BitVec.getElem_ushiftRight,
      leftElem, rightBit] at bitEq
  · intro noGap
    apply BitVec.eq_of_getElem_eq
    intro index index_lt
    let left : Fin order := ⟨index, index_lt⟩
    by_cases leftMember : left ∈ decodeCode leftCode
    · by_cases right_lt : gap + index < order
      · let right : Fin order := ⟨gap + index, right_lt⟩
        have rightNotMember : right ∉ decodeCode rightCode := by
          intro rightMember
          have forbidden := noGap left leftMember right rightMember (by
            change index < gap + index
            omega)
          apply forbidden
          change (gap + index) - index = gap
          omega
        have rightBit : rightCode.getLsbD (gap + index) = false := by
          rw [BitVec.getLsbD_eq_getElem right_lt]
          simpa [decodeCode, right] using rightNotMember
        simp [BitVec.getElem_and, BitVec.getElem_ushiftRight, rightBit]
      · have rightBit : rightCode.getLsbD (gap + index) = false := by
          apply BitVec.getLsbD_of_ge
          omega
        simp [BitVec.getElem_and, BitVec.getElem_ushiftRight, rightBit]
    · have leftBit : leftCode.getLsb left = false := by
        simpa [decodeCode] using leftMember
      have leftElem : leftCode[index] = false := by
        simpa [left, BitVec.getLsb_eq_getElem] using leftBit
      simp [BitVec.getElem_and, BitVec.getElem_ushiftRight, leftElem]

/-- An unshifted intersection is zero exactly when the decoded labels have no
common position. -/
theorem and_eq_zero_iff_no_common {order : Nat}
    (leftCode rightCode : LabelCode order) :
    leftCode &&& rightCode = 0 ↔
      ∀ position : Fin order,
        position ∈ decodeCode leftCode → position ∉ decodeCode rightCode := by
  constructor
  · intro zero position leftMember rightMember
    have bitEq := congrArg (fun bits : LabelCode order => bits[position.1]) zero
    have leftBit : leftCode[position.1] = true := by
      simpa [decodeCode, BitVec.getLsb_eq_getElem] using leftMember
    have rightBit : rightCode[position.1] = true := by
      simpa [decodeCode, BitVec.getLsb_eq_getElem] using rightMember
    simp [BitVec.getElem_and, leftBit, rightBit] at bitEq
  · intro disjoint
    apply BitVec.eq_of_getElem_eq
    intro index index_lt
    let position : Fin order := ⟨index, index_lt⟩
    by_cases leftMember : position ∈ decodeCode leftCode
    · have rightNotMember := disjoint position leftMember
      have rightBit : rightCode[index] = false := by
        simpa [decodeCode, position, BitVec.getLsb_eq_getElem] using rightNotMember
      simp [BitVec.getElem_and, rightBit]
    · have leftBit : leftCode[index] = false := by
        simpa [decodeCode, position, BitVec.getLsb_eq_getElem] using leftMember
      simp [BitVec.getElem_and, leftBit]

/-- Length of the cycle closed by an outside vertex attached at two ordered
path positions. -/
def pairCycleLength {order : Nat} (left right : Fin order) : Nat :=
  right.1 - left.1 + 2

/-- A nonempty attachment label is legal when no ordered pair of its
positions closes an accepted cycle length. -/
def Legal (order : Nat) (LengthOK : Nat → Prop) (label : Label order) : Prop :=
  label.Nonempty ∧
    ∀ left ∈ label, ∀ right ∈ label, left < right →
      ¬LengthOK (pairCycleLength left right)

/-- Pointwise decision procedure for legal labels. -/
def legalDecidable (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (label : Label order) : Decidable (Legal order LengthOK label) := by
  unfold Legal pairCycleLength
  letI : DecidablePred LengthOK := lengthDecidable
  infer_instance

/-- Reusable exact-classification profile for all legal attachment labels. -/
def classificationProfile (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length)) :
    CT10.ExhaustiveClassification.Profile (Label order) where
  candidates := labels order
  Accepts := Legal order LengthOK
  acceptsDecidable := legalDecidable order LengthOK lengthDecidable

/-- An executable finite classifier whose acceptance predicate is proved
equivalent to graph-theoretic legality.  This permits an application to use a
cheaper local normal form without changing the classified objects. -/
structure Classification (order : Nat) (LengthOK : Nat → Prop) where
  Candidate : Type
  profile : CT10.ExhaustiveClassification.Profile Candidate
  decode : Candidate ≃ Label order
  accepts_iff_legal : ∀ candidate, profile.Accepts candidate ↔
    Legal order LengthOK (decode candidate)

/-- Canonical classifier using `Legal` itself. -/
def canonicalClassification (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length)) :
    Classification order LengthOK where
  Candidate := Label order
  profile := classificationProfile order LengthOK lengthDecidable
  decode := Equiv.refl _
  accepts_iff_legal := fun _label => Iff.rfl

/-- Cross-label cycle length after inserting a connector of scale `shift`. -/
def positionDistance {order : Nat} (left right : Fin order) : Nat :=
  max left.1 right.1 - min left.1 right.1

/-- Cross-label cycle length after inserting a connector of scale `shift`. -/
def crossCycleLength {order : Nat} (shift : Nat)
    (left right : Fin order) : Nat :=
  shift + 2 + positionDistance left right

/-- Two labels are compatible at scale `shift` when no pair of their
positions closes an accepted cycle length. -/
def Compatible (order : Nat) (LengthOK : Nat → Prop) (shift : Nat)
    (left right : Label order) : Prop :=
  ∀ leftPosition ∈ left, ∀ rightPosition ∈ right,
    ¬LengthOK (crossCycleLength shift leftPosition rightPosition)

/-- Pointwise decision procedure for the finite compatibility relation. -/
def compatibleDecidable (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (shift : Nat) (left right : Label order) :
    Decidable (Compatible order LengthOK shift left right) := by
  unfold Compatible crossCycleLength
  letI : DecidablePred LengthOK := lengthDecidable
  infer_instance

/-- The manuscript's zero-one compatibility coefficient `C_shift`. -/
def C (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (shift : Nat) (left right : Label order) : Nat :=
  @ite Nat (Compatible order LengthOK shift left right)
    (compatibleDecidable order LengthOK lengthDecidable shift left right) 1 0

theorem C_eq_one_iff (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (shift : Nat) (left right : Label order) :
    C order LengthOK lengthDecidable shift left right = 1 ↔
      Compatible order LengthOK shift left right := by
  classical
  simp [C]

theorem C_eq_zero_iff (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (shift : Nat) (left right : Label order) :
    C order LengthOK lengthDecidable shift left right = 0 ↔
      ¬Compatible order LengthOK shift left right := by
  classical
  simp [C]

theorem C_le_one (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (shift : Nat) (left right : Label order) :
    C order LengthOK lengthDecidable shift left right ≤ 1 := by
  unfold C
  split <;> omega

/-- The two-step curvature indicator
`C₁(S,A) C₁(A,T) (1-C₂(S,T))`. -/
def omegaTwo (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (source middle target : Label order) : Nat :=
  C order LengthOK lengthDecidable 1 source middle *
    C order LengthOK lengthDecidable 1 middle target *
      (1 - C order LengthOK lengthDecidable 2 source target)

theorem omegaTwo_eq_one_iff (order : Nat) (LengthOK : Nat → Prop)
    (lengthDecidable : (length : Nat) → Decidable (LengthOK length))
    (source middle target : Label order) :
    omegaTwo order LengthOK lengthDecidable source middle target = 1 ↔
      Compatible order LengthOK 1 source middle ∧
      Compatible order LengthOK 1 middle target ∧
      ¬Compatible order LengthOK 2 source target := by
  classical
  simp only [omegaTwo, C]
  split_ifs <;> simp_all

/-! ## Labels of actual path attachments -/

/-- Positions of a labelled induced path adjacent to one ambient vertex. -/
def attachmentLabel {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    [DecidableRel G.Adj] (path : SimpleGraph.pathGraph order ↪g G)
    (vertex : V) : Label order :=
  Finset.univ.filter fun position => G.Adj vertex (path position)

@[simp] theorem mem_attachmentLabel_iff
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    [DecidableRel G.Adj] (path : SimpleGraph.pathGraph order ↪g G)
    (vertex : V) (position : Fin order) :
    position ∈ attachmentLabel path vertex ↔
      G.Adj vertex (path position) := by
  simp [attachmentLabel]

/-- An ambient vertex with at least one path neighbour has a nonempty
attachment label. -/
theorem attachmentLabel_nonempty
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    [DecidableRel G.Adj] (path : SimpleGraph.pathGraph order ↪g G)
    (vertex : V) (attached : ∃ position, G.Adj vertex (path position)) :
    (attachmentLabel path vertex).Nonempty := by
  obtain ⟨position, adjacent⟩ := attached
  exact ⟨position, (mem_attachmentLabel_iff path vertex position).2 adjacent⟩

/-- Attachment label computed from the adjacency decision procedure carried
by a finite graph object. -/
def finiteObjectAttachmentLabel {V : Type uVertex} (object : FiniteObject V)
    {order : Nat} (path : SimpleGraph.pathGraph order ↪g object.graph)
    (vertex : V) : Label order := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact attachmentLabel path vertex

/-! ## Cycle certificate closed by two attachments -/

/-- Canonical forward walk through consecutive vertices of a path graph. -/
private def forwardWalk {order : Nat} (start : Nat) :
    (gap : Nat) → (bound : start + gap < order) →
      (SimpleGraph.pathGraph order).Walk
        ⟨start, lt_of_le_of_lt (Nat.le_add_right start gap) bound⟩
        ⟨start + gap, bound⟩
  | 0, bound => .nil
  | gap + 1, bound =>
      (forwardWalk start gap (by omega)).concat (by
        rw [SimpleGraph.pathGraph_adj]
        left
        change start + gap + 1 = start + (gap + 1)
        omega)

private theorem forwardWalk_length {order start gap : Nat}
    (bound : start + gap < order) :
    (forwardWalk start gap bound).length = gap := by
  induction gap with
  | zero => rfl
  | succ gap inductionHypothesis =>
      simp only [forwardWalk, SimpleGraph.Walk.length_concat,
        inductionHypothesis]

private theorem forwardWalk_support_le {order start gap : Nat}
    (bound : start + gap < order) (position : Fin order)
    (member : position ∈ (forwardWalk start gap bound).support) :
    position.1 ≤ start + gap := by
  induction gap with
  | zero =>
      have equal : position =
          ⟨start, lt_of_le_of_lt (Nat.le_refl start) bound⟩ := by
        simpa [forwardWalk] using member
      subst position
      exact Nat.le_refl start
  | succ gap inductionHypothesis =>
      simp only [forwardWalk, SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at member
      rcases member with member | equal
      · exact (inductionHypothesis (by omega) member).trans (by omega)
      · cases equal
        exact Nat.le_refl _

private theorem forwardWalk_support_ge {order start gap : Nat}
    (bound : start + gap < order) (position : Fin order)
    (member : position ∈ (forwardWalk start gap bound).support) :
    start ≤ position.1 := by
  induction gap with
  | zero =>
      have equal : position =
          ⟨start, lt_of_le_of_lt (Nat.le_refl start) bound⟩ := by
        simpa [forwardWalk] using member
      subst position
      exact Nat.le_refl start
  | succ gap inductionHypothesis =>
      simp only [forwardWalk, SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at member
      rcases member with member | equal
      · exact inductionHypothesis (by omega) member
      · cases equal
        exact Nat.le_add_right start (gap + 1)

private theorem forwardWalk_isPath {order start gap : Nat}
    (bound : start + gap < order) :
    (forwardWalk start gap bound).IsPath := by
  induction gap with
  | zero => simp [forwardWalk]
  | succ gap inductionHypothesis =>
      apply (inductionHypothesis (by omega)).concat
      intro member
      have upper : start + (gap + 1) ≤ start + gap :=
        forwardWalk_support_le (start := start) (gap := gap)
          (by omega) ⟨start + (gap + 1), bound⟩ member
      omega

/-- Consecutive path-graph walk between two ordered positions. -/
private def segmentWalk {order : Nat} (left right : Fin order)
    (left_le_right : left ≤ right) :
    (SimpleGraph.pathGraph order).Walk left right :=
  (forwardWalk left.1 (right.1 - left.1) (by omega)).copy
    (by apply Fin.ext; rfl)
    (by
      apply Fin.ext
      exact Nat.add_sub_of_le left_le_right)

private theorem segmentWalk_length {order : Nat} (left right : Fin order)
    (left_le_right : left ≤ right) :
    (segmentWalk left right left_le_right).length = right.1 - left.1 := by
  simp [segmentWalk, forwardWalk_length]

private theorem segmentWalk_isPath {order : Nat} (left right : Fin order)
    (left_le_right : left ≤ right) :
    (segmentWalk left right left_le_right).IsPath := by
  unfold segmentWalk
  rw [SimpleGraph.Walk.isPath_copy]
  exact forwardWalk_isPath _

private theorem segmentWalk_support_bounds {order : Nat}
    (left right position : Fin order) (left_le_right : left ≤ right)
    (member : position ∈ (segmentWalk left right left_le_right).support) :
    left ≤ position ∧ position ≤ right := by
  unfold segmentWalk at member
  rw [SimpleGraph.Walk.support_copy] at member
  constructor
  · exact forwardWalk_support_ge (by omega) position member
  · have upper := forwardWalk_support_le (by omega) position member
    exact_mod_cast (show position.1 ≤ right.1 by omega)

/-- The literal path segment transported through an induced-path embedding. -/
def ambientSegment {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (left right : Fin order) (left_le_right : left ≤ right) :
    G.Walk (path left) (path right) :=
  (segmentWalk left right left_le_right).map path.toHom

theorem ambientSegment_length
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (left right : Fin order) (left_le_right : left ≤ right) :
    (ambientSegment path left right left_le_right).length =
      right.1 - left.1 := by
  simp [ambientSegment, segmentWalk_length]

theorem ambientSegment_isPath
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (left right : Fin order) (left_le_right : left ≤ right) :
    (ambientSegment path left right left_le_right).IsPath :=
  SimpleGraph.Walk.map_isPath_of_injective path.injective
    (segmentWalk_isPath left right left_le_right)

/-- A vertex outside the embedded path does not occur on any transported
path segment.  This support lemma is the reusable interface needed by local
cycle constructors with two external endpoints. -/
theorem outside_not_mem_ambientSegment
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (outsidePath : ∀ position : Fin order, outside ≠ path position)
    (left right : Fin order) (left_le_right : left ≤ right) :
    outside ∉ (ambientSegment path left right left_le_right).support := by
  intro outsideMember
  rw [ambientSegment, SimpleGraph.Walk.support_map] at outsideMember
  obtain ⟨position, _positionMember, equal⟩ := List.mem_map.mp outsideMember
  exact outsidePath position equal.symm

/-- Every vertex on a transported segment comes from a path position in the
closed index interval between its endpoints. -/
theorem mem_ambientSegment_support_bounds
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G)
    (left right : Fin order) (left_le_right : left ≤ right) (vertex : V)
    (member : vertex ∈ (ambientSegment path left right left_le_right).support) :
    ∃ position : Fin order,
      path position = vertex ∧ left ≤ position ∧ position ≤ right := by
  rw [ambientSegment, SimpleGraph.Walk.support_map] at member
  obtain ⟨position, positionMember, equal⟩ := List.mem_map.mp member
  exact ⟨position, equal, segmentWalk_support_bounds left right position
    left_le_right positionMember⟩

/-- Return from the left attachment along the path segment and then to the
outside vertex. -/
def attachmentReturn {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (left right : Fin order) (left_le_right : left ≤ right)
    (rightAdjacent : G.Adj outside (path right)) :
    G.Walk (path left) outside :=
  (ambientSegment path left right left_le_right).concat rightAdjacent.symm

theorem attachmentReturn_length
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (left right : Fin order) (left_le_right : left ≤ right)
    (rightAdjacent : G.Adj outside (path right)) :
    (attachmentReturn path outside left right left_le_right
      rightAdjacent).length = right.1 - left.1 + 1 := by
  simp [attachmentReturn, ambientSegment_length]

theorem attachmentReturn_isPath
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (outsidePath : ∀ position : Fin order, outside ≠ path position)
    (left right : Fin order) (left_le_right : left ≤ right)
    (rightAdjacent : G.Adj outside (path right)) :
    (attachmentReturn path outside left right left_le_right
      rightAdjacent).IsPath := by
  apply (ambientSegment_isPath path left right left_le_right).concat
  intro outsideMember
  rw [ambientSegment, SimpleGraph.Walk.support_map] at outsideMember
  obtain ⟨position, _positionMember, equal⟩ := List.mem_map.mp outsideMember
  exact outsidePath position equal.symm

/-- Close the attachment return by the edge from the outside vertex to the
left path position. -/
def attachmentCycleWalk
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (left right : Fin order) (left_le_right : left ≤ right)
    (leftAdjacent : G.Adj outside (path left))
    (rightAdjacent : G.Adj outside (path right)) :
    G.Walk outside outside :=
  SimpleGraph.Walk.cons leftAdjacent
    (attachmentReturn path outside left right left_le_right rightAdjacent)

theorem attachmentCycleWalk_isCycle
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (outsidePath : ∀ position : Fin order, outside ≠ path position)
    (left right : Fin order) (left_lt_right : left < right)
    (leftAdjacent : G.Adj outside (path left))
    (rightAdjacent : G.Adj outside (path right)) :
    (attachmentCycleWalk path outside left right left_lt_right.le
      leftAdjacent rightAdjacent).IsCycle := by
  rw [attachmentCycleWalk, SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · exact attachmentReturn_isPath path outside outsidePath left right
      left_lt_right.le rightAdjacent
  · intro edgeMember
    have swapped : s(path left, outside) ∈
        (attachmentReturn path outside left right left_lt_right.le
          rightAdjacent).edges := by
      rwa [Sym2.eq_swap]
    have lengthOne :=
      (attachmentReturn_isPath path outside outsidePath left right
        left_lt_right.le rightAdjacent).length_eq_one_of_mem_edges swapped
    have exactLength := attachmentReturn_length path outside left right
      left_lt_right.le rightAdjacent
    omega

theorem attachmentCycleWalk_length
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (left right : Fin order) (left_lt_right : left < right)
    (leftAdjacent : G.Adj outside (path left))
    (rightAdjacent : G.Adj outside (path right)) :
    (attachmentCycleWalk path outside left right left_lt_right.le
      leftAdjacent rightAdjacent).length = pairCycleLength left right := by
  simp [attachmentCycleWalk, attachmentReturn_length, pairCycleLength]

/-- Two path attachments close an exact accepted cycle. -/
def cycleOfAttachments
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (LengthOK : Nat → Prop)
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (outsidePath : ∀ position : Fin order, outside ≠ path position)
    (left right : Fin order) (left_lt_right : left < right)
    (leftAdjacent : G.Adj outside (path left))
    (rightAdjacent : G.Adj outside (path right))
    (lengthOK : LengthOK (pairCycleLength left right)) :
    CycleWithLength G LengthOK where
  vertex := outside
  walk := attachmentCycleWalk path outside left right left_lt_right.le
    leftAdjacent rightAdjacent
  isCycle := attachmentCycleWalk_isCycle path outside outsidePath left right
    left_lt_right leftAdjacent rightAdjacent
  length_ok := by
    rw [attachmentCycleWalk_length path outside left right left_lt_right
      leftAdjacent rightAdjacent]
    exact lengthOK

/-- Target avoidance makes every nonempty actual attachment label legal. -/
theorem attachmentLabel_legal_of_avoids
    {V : Type uVertex} {G : SimpleGraph V} {order : Nat}
    (LengthOK : Nat → Prop) [DecidableRel G.Adj]
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V)
    (outsidePath : ∀ position : Fin order, outside ≠ path position)
    (attached : ∃ position, G.Adj outside (path position))
    (avoids : ¬HasCycleWithLength G LengthOK) :
    Legal order LengthOK (attachmentLabel path outside) := by
  refine ⟨attachmentLabel_nonempty path outside attached, ?_⟩
  intro left leftMember right rightMember left_lt_right lengthOK
  have leftAdjacent := (mem_attachmentLabel_iff path outside left).1 leftMember
  have rightAdjacent := (mem_attachmentLabel_iff path outside right).1 rightMember
  exact avoids ⟨cycleOfAttachments LengthOK path outside outsidePath left right
    left_lt_right leftAdjacent rightAdjacent lengthOK⟩

/-- Finite-object form of `attachmentLabel_legal_of_avoids`; applications do
not need to install the object's adjacency instance in theorem statements. -/
theorem finiteObjectAttachmentLabel_legal_of_avoids
    {V : Type uVertex} (object : FiniteObject V) {order : Nat}
    (LengthOK : Nat → Prop)
    (path : SimpleGraph.pathGraph order ↪g object.graph) (outside : V)
    (outsidePath : ∀ position : Fin order, outside ≠ path position)
    (attached : ∃ position, object.graph.Adj outside (path position))
    (avoids : ¬HasCycleWithLength object.graph LengthOK) :
    Legal order LengthOK
      (finiteObjectAttachmentLabel object path outside) := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact attachmentLabel_legal_of_avoids LengthOK path outside outsidePath
    attached avoids

/-- Every nonempty outside attachment to an induced edge in a triangle-free
graph is a legal two-position attachment label. -/
theorem finiteObjectEdgeAttachment_legal_of_cliqueFree
    {V : Type uVertex} (object : FiniteObject V)
    (triangleFree : object.graph.CliqueFree 3)
    (path : SimpleGraph.pathGraph 2 ↪g object.graph) (outside : V)
    (outsidePath : ∀ position : Fin 2, outside ≠ path position)
    (attached : ∃ position, object.graph.Adj outside (path position)) :
    Legal 2 TriangleLength
      (finiteObjectAttachmentLabel object path outside) :=
  finiteObjectAttachmentLabel_legal_of_avoids object TriangleLength path
    outside outsidePath attached
      (not_hasCycleWithTriangleLength_of_cliqueFree triangleFree)

end StructuralExhaustion.Graph.InducedPathAttachment
