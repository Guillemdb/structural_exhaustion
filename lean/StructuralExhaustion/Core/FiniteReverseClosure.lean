import StructuralExhaustion.Core.FiniteSearch
import Mathlib

namespace StructuralExhaustion.Core.FiniteReverseClosure

open scoped Sym2

universe uItem uKey

/-! # Reverse closure on one explicit finite ledger -/

structure Profile (Item : Type uItem) (Key : Type uKey) where
  items : List Item
  nodup : items.Nodup
  key : Item → Key
  reverse : Item → Key
  keyDecidableEq : DecidableEq Key
  keyInjective : ∀ {left right}, left ∈ items → right ∈ items →
    key left = key right → left = right
  reverse_ne : ∀ item ∈ items, reverse item ≠ key item

namespace Profile

variable {Item : Type uItem} {Key : Type uKey} (profile : Profile Item Key)

def keys : List Key := profile.items.map profile.key

def reversePresent (item : Item) : Prop := profile.reverse item ∈ profile.keys

noncomputable def reversePresentDecidable (item : Item) :
    Decidable (profile.reversePresent item) := by
  classical
  exact inferInstance

noncomputable def closedItems : List Item :=
  profile.items.filter fun item =>
    @decide (profile.reversePresent item) (profile.reversePresentDecidable item)

noncomputable def missingItems : List Item :=
  profile.items.filter fun item =>
    @decide (¬ profile.reversePresent item)
      (@instDecidableNot (profile.reversePresent item)
        (profile.reversePresentDecidable item))

theorem mem_missingItems_iff (item : Item) :
    item ∈ profile.missingItems ↔
      item ∈ profile.items ∧ ¬ profile.reversePresent item := by
  classical
  simp [missingItems]

theorem missingItems_nodup : profile.missingItems.Nodup :=
  profile.nodup.filter _

theorem closedItems_nodup : profile.closedItems.Nodup := profile.nodup.filter _

def pair (item : Item) : Sym2 Key := s(profile.key item, profile.reverse item)

noncomputable def pairLabels : List (Sym2 Key) := by
  classical
  exact (profile.closedItems.map profile.pair).dedup

inductive Outcome where
  | allClosed (closed : ∀ item ∈ profile.items, profile.reversePresent item)
  | firstMissing
      (hit : Core.FiniteSearch.FirstHit profile.items
        (fun item => ¬ profile.reversePresent item))

noncomputable def run : profile.Outcome :=
  match Core.FiniteSearch.firstOnList profile.items
      (fun item => ¬ profile.reversePresent item)
      (fun item => @instDecidableNot (profile.reversePresent item)
        (profile.reversePresentDecidable item)) with
  | .found hit => .firstMissing hit
  | .absent absent => .allClosed fun item member => by
      by_contra missing
      exact absent item member missing

theorem run_exhaustive :
    (∀ item ∈ profile.items, profile.reversePresent item) ∨
      (∃ hit : Core.FiniteSearch.FirstHit profile.items
        (fun item => ¬ profile.reversePresent item), True) := by
  cases profile.run with
  | allClosed closed => exact Or.inl closed
  | firstMissing hit => exact Or.inr ⟨hit, trivial⟩

private theorem fibre_length_le_two (label : Sym2 Key) :
    (profile.closedItems.filter fun item =>
      @decide (profile.pair item = label)
        (Classical.decEq (Sym2 Key) (profile.pair item) label)).length ≤ 2 := by
  classical
  let fibre := profile.closedItems.filter fun item =>
    @decide (profile.pair item = label)
      (Classical.decEq (Sym2 Key) (profile.pair item) label)
  have fibreNodup : fibre.Nodup := profile.closedItems_nodup.filter _
  have keyNodup : (fibre.map profile.key).Nodup := by
    apply List.Nodup.map_on
    · intro left leftMem right rightMem equal
      have leftClosed : left ∈ profile.items := by
        exact List.mem_of_mem_filter (List.mem_of_mem_filter leftMem)
      have rightClosed : right ∈ profile.items := by
        exact List.mem_of_mem_filter (List.mem_of_mem_filter rightMem)
      exact profile.keyInjective leftClosed rightClosed equal
    · exact fibreNodup
  induction label using Sym2.inductionOn with
  | _ first second =>
      have subset : (fibre.map profile.key).toFinset ⊆
          ({first, second} : Finset Key) := by
        intro keyValue member
        rw [List.mem_toFinset, List.mem_map] at member
        rcases member with ⟨item, itemMem, rfl⟩
        have pairEq : profile.pair item = s(first, second) := by
          simpa using (List.mem_filter.mp itemMem).2
        simp only [pair, Sym2.eq_iff] at pairEq
        rcases pairEq with pairEq | pairEq
        · simp [pairEq.1]
        · simp [pairEq.1]
      change fibre.length ≤ 2
      rw [← List.length_map profile.key,
        ← List.toFinset_card_of_nodup keyNodup]
      have pairCard : ({first, second} : Finset Key).card ≤ 2 := by
        have inserted := Finset.card_insert_le first ({second} : Finset Key)
        simpa using inserted
      exact (Finset.card_le_card subset).trans pairCard

/-- Exact factor-two bound on the proof-carrying reverse-closed subledger.
The label universe is only the unordered pairs actually occurring there. -/
theorem closedItems_le_two_mul_pairLabels :
    profile.closedItems.length ≤ 2 * (pairLabels profile).length := by
  classical
  let itemsFinset := profile.closedItems.toFinset
  let labelsFinset := (pairLabels profile).toFinset
  have mapsTo : (itemsFinset : Set Item).MapsTo profile.pair labelsFinset := by
    intro item member
    change item ∈ itemsFinset at member
    change profile.pair item ∈ labelsFinset
    have member' : item ∈ profile.closedItems := by
      simpa [itemsFinset] using member
    simp only [labelsFinset, pairLabels, List.mem_toFinset, List.mem_dedup,
      List.mem_map]
    exact ⟨item, member', rfl⟩
  have partition := Finset.card_eq_sum_card_fiberwise mapsTo
  rw [List.toFinset_card_of_nodup profile.closedItems_nodup] at partition
  unfold pairLabels
  rw [← List.toFinset_card_of_nodup
    (List.nodup_dedup (profile.closedItems.map profile.pair))]
  calc
    profile.closedItems.length =
        ∑ label ∈ labelsFinset,
          (itemsFinset.filter fun item => profile.pair item = label).card := partition
    _ ≤ ∑ _label ∈ labelsFinset, 2 := by
      apply Finset.sum_le_sum
      intro label _member
      have fibreCard :
          (itemsFinset.filter fun item => profile.pair item = label).card =
            (profile.closedItems.filter fun item =>
              @decide (profile.pair item = label)
                (Classical.decEq (Sym2 Key) (profile.pair item) label)).length := by
        rw [← List.toFinset_card_of_nodup
          (profile.closedItems_nodup.filter fun item =>
            @decide (profile.pair item = label)
              (Classical.decEq (Sym2 Key) (profile.pair item) label))]
        congr 1
        ext item
        simp [itemsFinset]
      rw [fibreCard]
      exact profile.fibre_length_le_two label
    _ = 2 * labelsFinset.card := by simp [Nat.mul_comm]

def visibleChecks : Nat := profile.items.length ^ 2

end Profile

end StructuralExhaustion.Core.FiniteReverseClosure
