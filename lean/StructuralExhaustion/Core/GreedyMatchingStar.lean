import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.WorkBudget
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace StructuralExhaustion.Core.GreedyMatchingStar

open StructuralExhaustion

universe u

/-!
# Polynomial matching--star extraction on an ordered pair schedule

This module works only with an already supplied duplicate-free list of
canonically oriented pairs.  It constructs one greedy maximal matching and
uses endpoint-incidence counts to obtain the sharp elementary bound

`(L - 1) * (2 * L - 3)`.

The construction never enumerates matchings, stars, subsets, or ambient
graphs.  The only filters are over the supplied pair list.
-/

variable {Vertex : Type u} (vertices : FinEnum Vertex)

abbrev Pair := Enumeration.OrderedDistinctPair vertices

namespace Pair

def first (pair : Pair vertices) : Vertex :=
  Enumeration.OrderedDistinctPair.first pair

def second (pair : Pair vertices) : Vertex :=
  Enumeration.OrderedDistinctPair.second pair

theorem distinct (pair : Pair vertices) : pair.first ≠ pair.second :=
  Enumeration.OrderedDistinctPair.distinct pair

theorem ext {left right : Pair vertices}
    (first : left.first = right.first)
    (second : left.second = right.second) : left = right := by
  apply Subtype.ext
  exact Prod.ext first second

end Pair

def Touches (vertex : Vertex) (pair : Pair vertices) : Prop :=
  vertex = pair.first ∨ vertex = pair.second

def Intersects (left right : Pair vertices) : Prop :=
  Touches vertices left.first right ∨ Touches vertices left.second right

def Disjoint (left right : Pair vertices) : Prop :=
  ¬Intersects vertices left right

instance touchesDecidable (vertex : Vertex) (pair : Pair vertices) :
    Decidable (Touches vertices vertex pair) := by
  letI : DecidableEq Vertex := vertices.decEq
  unfold Touches
  exact inferInstance

instance intersectsDecidable (left right : Pair vertices) :
    Decidable (Intersects vertices left right) := by
  letI : DecidableEq Vertex := vertices.decEq
  unfold Intersects Touches
  exact inferInstance

instance disjointDecidable (left right : Pair vertices) :
    Decidable (Disjoint vertices left right) := by
  letI : DecidableEq Vertex := vertices.decEq
  unfold Disjoint Intersects Touches
  exact inferInstance

theorem touches_self_first (pair : Pair vertices) :
    Touches vertices pair.first pair := Or.inl rfl

theorem touches_self_second (pair : Pair vertices) :
    Touches vertices pair.second pair := Or.inr rfl

theorem intersects_self (pair : Pair vertices) :
    Intersects vertices pair pair := Or.inl (touches_self_first vertices pair)

theorem intersects_symm {left right : Pair vertices}
    (intersects : Intersects vertices left right) :
    Intersects vertices right left := by
  rcases intersects with
    (firstFirst | firstSecond) | (secondFirst | secondSecond)
  · exact Or.inl (Or.inl firstFirst.symm)
  · exact Or.inr (Or.inl firstSecond.symm)
  · exact Or.inl (Or.inr secondFirst.symm)
  · exact Or.inr (Or.inr secondSecond.symm)

theorem disjoint_symm {left right : Pair vertices}
    (disjoint : Disjoint vertices left right) :
    Disjoint vertices right left := by
  intro intersects
  exact disjoint (intersects_symm vertices intersects)

/-- Test whether one pair is disjoint from every pair already selected. -/
def compatible (pair : Pair vertices) (selected : List (Pair vertices)) : Bool :=
  selected.all fun candidate => decide (Disjoint vertices pair candidate)

theorem compatible_eq_true_iff (pair : Pair vertices)
    (selected : List (Pair vertices)) :
    compatible vertices pair selected = true ↔
      ∀ candidate ∈ selected, Disjoint vertices pair candidate := by
  simp [compatible]

/-- Greedy maximal matching on the supplied list.  Recursion is structural on
the tail, so execution uses one triangular scan of the supplied pairs. -/
def greedy : List (Pair vertices) → List (Pair vertices)
  | [] => []
  | pair :: tail =>
      let selected := greedy tail
      if compatible vertices pair selected then pair :: selected else selected

theorem greedy_sublist : ∀ pairs : List (Pair vertices),
    (greedy vertices pairs).Sublist pairs := by
  intro pairs
  induction pairs with
  | nil => simp [greedy]
  | cons pair tail ih =>
      simp only [greedy]
      split
      · exact ih.cons_cons pair
      · exact ih.trans (List.tail_sublist (pair :: tail))

theorem greedy_nodup {pairs : List (Pair vertices)} (nodup : pairs.Nodup) :
    (greedy vertices pairs).Nodup :=
  nodup.sublist (greedy_sublist vertices pairs)

theorem greedy_pairwise : ∀ pairs : List (Pair vertices),
    (greedy vertices pairs).Pairwise (Disjoint vertices) := by
  intro pairs
  induction pairs with
  | nil => simp [greedy]
  | cons pair tail ih =>
      simp only [greedy]
      split <;> rename_i decision
      · rw [List.pairwise_cons]
        exact ⟨(compatible_eq_true_iff vertices pair _).1 decision, ih⟩
      · exact ih

/-- Every supplied pair meets a selected greedy pair. -/
theorem greedy_covers : ∀ (pairs : List (Pair vertices))
    (pair : Pair vertices), pair ∈ pairs →
      ∃ selected ∈ greedy vertices pairs,
        Intersects vertices pair selected := by
  intro pairs candidate member
  induction pairs generalizing candidate with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [greedy]
      split <;> rename_i decision
      · rcases member with rfl | tailMember
        · exact ⟨candidate, by simp, intersects_self vertices candidate⟩
        · obtain ⟨selected, selectedMem, intersects⟩ := ih candidate tailMember
          exact ⟨selected, by simp [selectedMem], intersects⟩
      · have notAll : ¬∀ selected ∈ greedy vertices tail,
            Disjoint vertices head selected := by
          intro allDisjoint
          exact decision ((compatible_eq_true_iff vertices head _).2 allDisjoint)
        push Not at notAll
        rcases member with rfl | tailMember
        · obtain ⟨selected, selectedMem, notDisjoint⟩ := notAll
          exact ⟨selected, selectedMem,
            not_not.mp notDisjoint⟩
        · exact ih candidate tailMember

def IsMatching (pairs : List (Pair vertices)) : Prop :=
  pairs.Nodup ∧ pairs.Pairwise (Disjoint vertices)

def IsStar (center : Vertex) (pairs : List (Pair vertices)) : Prop :=
  pairs.Nodup ∧ ∀ pair ∈ pairs, Touches vertices center pair

structure Matching (source : OrderedCollection (Pair vertices))
    (size : Nat) where
  pairs : List (Pair vertices)
  sublist : pairs.Sublist source.values
  exactSize : pairs.length = size
  matching : IsMatching vertices pairs

structure Star (source : OrderedCollection (Pair vertices)) (size : Nat) where
  center : Vertex
  pairs : List (Pair vertices)
  sublist : pairs.Sublist source.values
  exactSize : pairs.length = size
  star : IsStar vertices center pairs

inductive Pattern (source : OrderedCollection (Pair vertices)) (size : Nat)
    where
  | matching (result : Matching vertices source size)
  | star (result : Star vertices source size)

def matchingStarCap (size : Nat) : Nat :=
  (size - 1) * (2 * size - 3)

def incident (source : OrderedCollection (Pair vertices)) (vertex : Vertex) :
    Finset (Pair vertices) := by
  letI : DecidableEq (Pair vertices) :=
    (Enumeration.orderedDistinctPairs vertices).decEq
  exact source.values.toFinset.filter fun pair => Touches vertices vertex pair

def pairIncident (source : OrderedCollection (Pair vertices))
    (pair : Pair vertices) : Finset (Pair vertices) :=
  incident vertices source pair.first ∪ incident vertices source pair.second

theorem mem_incident_iff (source : OrderedCollection (Pair vertices))
    (vertex : Vertex) (pair : Pair vertices) :
    pair ∈ incident vertices source vertex ↔
      pair ∈ source.values ∧ Touches vertices vertex pair := by
  simp [incident]

theorem mem_pairIncident_iff (source : OrderedCollection (Pair vertices))
    (selected pair : Pair vertices) :
    pair ∈ pairIncident vertices source selected ↔
      pair ∈ source.values ∧ Intersects vertices selected pair := by
  simp only [pairIncident, Finset.mem_union, mem_incident_iff]
  constructor
  · rintro (⟨member, touches⟩ | ⟨member, touches⟩)
    · exact ⟨member, Or.inl touches⟩
    · exact ⟨member, Or.inr touches⟩
  · rintro ⟨member, touches | touches⟩
    · exact Or.inl ⟨member, touches⟩
    · exact Or.inr ⟨member, touches⟩

theorem source_subset_greedy_pairIncident
    (source : OrderedCollection (Pair vertices)) :
    source.values.toFinset ⊆
      (greedy vertices source.values).toFinset.biUnion
        (pairIncident vertices source) := by
  intro pair member
  have listMember : pair ∈ source.values := List.mem_toFinset.mp member
  obtain ⟨selected, selectedMem, intersects⟩ :=
    greedy_covers vertices source.values pair listMember
  apply Finset.mem_biUnion.mpr
  refine ⟨selected, List.mem_toFinset.mpr selectedMem, ?_⟩
  exact (mem_pairIncident_iff vertices source selected pair).2
    ⟨listMember, intersects_symm vertices intersects⟩

theorem exists_matching_of_size_le_greedy
    (source : OrderedCollection (Pair vertices)) {size : Nat}
    (large : size ≤ (greedy vertices source.values).length) :
    Nonempty (Matching vertices source size) := by
  let chosen := (greedy vertices source.values).take size
  refine ⟨{
    pairs := chosen
    sublist := (List.take_sublist _ _).trans (greedy_sublist vertices source.values)
    exactSize := List.length_take_of_le large
    matching := ?_ }⟩
  constructor
  · exact (greedy_nodup vertices source.nodup).sublist (List.take_sublist _ _)
  · exact (greedy_pairwise vertices source.values).sublist (List.take_sublist _ _)

theorem exists_star_of_incident_card
    (source : OrderedCollection (Pair vertices)) (center : Vertex) {size : Nat}
    (large : size ≤ (incident vertices source center).card) :
    Nonempty (Star vertices source size) := by
  let pairs := (source.values.filter fun pair =>
    Touches vertices center pair).take size
  have filterLength :
      (source.values.filter fun pair => Touches vertices center pair).length =
        (incident vertices source center).card := by
    unfold incident
    rw [← List.toFinset_card_of_nodup (source.nodup.filter _)]
    congr 1
    ext pair
    simp
  have lengthBound : size ≤
      (source.values.filter fun pair => Touches vertices center pair).length := by
    simpa [filterLength] using large
  refine ⟨{
    center := center
    pairs := pairs
    sublist := (List.take_sublist _ _).trans (List.filter_sublist)
    exactSize := by simp [pairs, lengthBound]
    star := ?_ }⟩
  constructor
  · exact (source.nodup.filter _).sublist (List.take_sublist _ _)
  · intro pair member
    have filtered : pair ∈
        source.values.filter fun edge => Touches vertices center edge :=
      (List.take_sublist _ _).subset member
    exact of_decide_eq_true (List.mem_filter.mp filtered).2

theorem incident_card_le_pred_of_no_star
    (source : OrderedCollection (Pair vertices)) {size : Nat}
    (noStar : IsEmpty (Star vertices source size))
    (center : Vertex) :
    (incident vertices source center).card ≤ size - 1 := by
  by_contra larger
  have sizeLe : size ≤ (incident vertices source center).card := by omega
  exact noStar.false
    (Classical.choice (exists_star_of_incident_card vertices source center sizeLe))

theorem pair_mem_both_incident
    (source : OrderedCollection (Pair vertices))
    {pair : Pair vertices} (member : pair ∈ source.values) :
    pair ∈ incident vertices source pair.first ∩
      incident vertices source pair.second := by
  simp [mem_incident_iff, member, touches_self_first,
    touches_self_second]

theorem pairIncident_card_le
    (source : OrderedCollection (Pair vertices)) {size : Nat}
    (twoLe : 2 ≤ size)
    (noStar : IsEmpty (Star vertices source size))
    {pair : Pair vertices} (member : pair ∈ source.values) :
    (pairIncident vertices source pair).card ≤ 2 * size - 3 := by
  let firstInc := incident vertices source pair.first
  let secondInc := incident vertices source pair.second
  have firstBound := incident_card_le_pred_of_no_star vertices source noStar pair.first
  have secondBound := incident_card_le_pred_of_no_star vertices source noStar pair.second
  change firstInc.card ≤ size - 1 at firstBound
  change secondInc.card ≤ size - 1 at secondBound
  have intersectionOne : 1 ≤ (firstInc ∩ secondInc).card := by
    exact Finset.card_pos.mpr ⟨pair,
      pair_mem_both_incident vertices source member⟩
  have unionIdentity := Finset.card_union_add_card_inter firstInc secondInc
  change (firstInc ∪ secondInc).card ≤ 2 * size - 3
  omega

/-- Sharp local matching--star theorem. -/
theorem exists_pattern_of_cap_lt_card
    (source : OrderedCollection (Pair vertices)) (size : Nat)
    (overloaded : matchingStarCap size < source.values.length) :
    Nonempty (Pattern vertices source size) := by
  by_cases sizeZero : size = 0
  · subst size
    exact ⟨.matching {
      pairs := []
      sublist := List.nil_sublist _
      exactSize := rfl
      matching := by simp [IsMatching] }⟩
  by_cases sizeOne : size = 1
  · subst size
    have nonempty : source.values ≠ [] := by
      intro empty
      simp [empty, matchingStarCap] at overloaded
    obtain ⟨pair, tail, sourceEq⟩ := List.exists_cons_of_ne_nil nonempty
    exact ⟨.star {
      center := pair.first
      pairs := [pair]
      sublist := by rw [sourceEq]; exact (List.nil_sublist tail).cons_cons pair
      exactSize := rfl
      star := by simp [IsStar, Touches] }⟩
  have twoLe : 2 ≤ size := by omega
  by_cases enoughMatching : size ≤ (greedy vertices source.values).length
  · exact Nonempty.map Pattern.matching
      (exists_matching_of_size_le_greedy vertices source enoughMatching)
  · have greedyBound : (greedy vertices source.values).length ≤ size - 1 := by
      omega
    by_cases hasStar : Nonempty (Star vertices source size)
    · exact Nonempty.map Pattern.star hasStar
    · have noStar : IsEmpty (Star vertices source size) :=
        ⟨fun star => hasStar ⟨star⟩⟩
      have greedyNodup := greedy_nodup vertices source.nodup
      have unionBound :
          ((greedy vertices source.values).toFinset.biUnion
            (pairIncident vertices source)).card ≤
              (greedy vertices source.values).toFinset.card * (2 * size - 3) := by
        apply Finset.card_biUnion_le_card_mul
        intro selected selectedMem
        apply pairIncident_card_le vertices source twoLe noStar
        exact (greedy_sublist vertices source.values).subset
          (List.mem_toFinset.mp selectedMem)
      have sourceBound : source.values.length ≤
          (greedy vertices source.values).length * (2 * size - 3) := by
        rw [← List.toFinset_card_of_nodup source.nodup,
          ← List.toFinset_card_of_nodup greedyNodup]
        exact (Finset.card_le_card
          (source_subset_greedy_pairIncident vertices source)).trans unionBound
      have capBound : source.values.length ≤ matchingStarCap size := by
        unfold matchingStarCap
        exact sourceBound.trans (Nat.mul_le_mul_right _ greedyBound)
      omega

/-- The extractor verifies a supplied fibre in quadratic time: the greedy
filter performs at most `m²` pair-intersection tests, and endpoint incidence
counts perform at most another `2m²` tests. -/
def checks (source : OrderedCollection (Pair vertices)) : Nat :=
  3 * source.values.length ^ 2

theorem checks_cubic (source : OrderedCollection (Pair vertices)) :
    checks vertices source ≤ 3 * (source.values.length + 1) ^ 2 := by
  unfold checks
  exact Nat.mul_le_mul_left 3
    (Nat.pow_le_pow_left (Nat.le_succ source.values.length) 2)

structure VerifiedStage (source : OrderedCollection (Pair vertices))
    (size : Nat) where
  overloaded : matchingStarCap size < source.values.length
  pattern : Pattern vertices source size
  polynomial : checks vertices source ≤ 3 * (source.values.length + 1) ^ 2

noncomputable def verifiedStage (source : OrderedCollection (Pair vertices))
    (size : Nat) (overloaded : matchingStarCap size < source.values.length) :
    VerifiedStage vertices source size where
  overloaded := overloaded
  pattern := Classical.choice
    (exists_pattern_of_cap_lt_card vertices source size overloaded)
  polynomial := checks_cubic vertices source

end StructuralExhaustion.Core.GreedyMatchingStar
