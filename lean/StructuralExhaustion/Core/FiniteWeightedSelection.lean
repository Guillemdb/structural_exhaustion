import Mathlib.Data.Fintype.Powerset
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteWeightedSelection

open scoped BigOperators

universe uItem uCarrier uLift

/-!
# Proof-level finite weighted selections

This module describes the finite candidate fibres used by refined ledgers.
The item universe is explicit, but the framework never materializes its
powerset.  A candidate is a proof-carrying `Finset` supplied by mathematics;
the `Finite` instance is used only by existence theorems such as finite choice.
-/

/-- Primitive data for a candidate that must contain prescribed items, avoid
forbidden items, and meet an additive lower bound. -/
structure Profile (Item : Type uItem) (Carrier : Type uCarrier) where
  items : FinEnum Item
  carrierDecidableEq : DecidableEq Carrier
  mandatory : Item → Prop
  mandatoryDecidable : ∀ item, Decidable (mandatory item)
  forbidden : Item → Prop
  forbiddenDecidable : ∀ item, Decidable (forbidden item)
  weight : Item → Int
  required : Int
  baseSupport : Finset Carrier
  itemSupport : Item → Finset Carrier

namespace Profile

variable {Item : Type uItem} {Carrier : Type uCarrier}
  (profile : Profile Item Carrier)

/-- Universe-lift the item type while preserving the exact finite order and
all selection semantics. -/
def uliftItems : Profile (ULift.{uLift, uItem} Item) Carrier where
  items := Core.Enumeration.ulift profile.items
  carrierDecidableEq := profile.carrierDecidableEq
  mandatory := fun item => profile.mandatory item.down
  mandatoryDecidable := fun item => profile.mandatoryDecidable item.down
  forbidden := fun item => profile.forbidden item.down
  forbiddenDecidable := fun item => profile.forbiddenDecidable item.down
  weight := fun item => profile.weight item.down
  required := profile.required
  baseSupport := profile.baseSupport
  itemSupport := fun item => profile.itemSupport item.down

/-- The exact predicate defining a valid candidate selection. -/
def Valid (selected : Finset Item) : Prop := by
  letI : DecidableEq Item := profile.items.decEq
  exact
    (∀ item, profile.mandatory item → item ∈ selected) ∧
    (∀ item, item ∈ selected → ¬profile.forbidden item) ∧
    profile.required ≤ ∑ item ∈ selected, profile.weight item

/-- A candidate is a finite item selection with all validity obligations
proved.  No enumeration of `Finset Item` is performed by this definition. -/
def Candidate := {selected : Finset Item // profile.Valid selected}

noncomputable instance candidateFinite : Finite profile.Candidate := by
  letI : FinEnum Item := profile.items
  letI : Fintype Item := inferInstance
  letI : Fintype (Finset Item) := Finset.fintype
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Carrier support consists of the fixed support and the support of every
selected item. -/
def carrierSupport (candidate : profile.Candidate) : Finset Carrier := by
  letI : DecidableEq Carrier := profile.carrierDecidableEq
  letI : DecidableEq Item := profile.items.decEq
  exact profile.baseSupport ∪ candidate.1.biUnion profile.itemSupport

theorem mandatory_mem (candidate : profile.Candidate) {item : Item}
    (mandatory : profile.mandatory item) : item ∈ candidate.1 :=
  candidate.2.1 item mandatory

theorem selected_not_forbidden (candidate : profile.Candidate) {item : Item}
    (selected : item ∈ candidate.1) : ¬profile.forbidden item :=
  candidate.2.2.1 item selected

theorem payment (candidate : profile.Candidate) :
    profile.required ≤ ∑ item ∈ candidate.1, profile.weight item :=
  candidate.2.2.2

/-- A supplied candidate cannot contain more items than the literal finite
item universe.  This is a cardinality theorem; it does not enumerate subsets. -/
theorem Candidate.card_le_items (candidate : profile.Candidate) :
    candidate.1.card ≤ profile.items.card := by
  letI : FinEnum Item := profile.items
  letI : DecidableEq Item := profile.items.decEq
  rw [FinEnum.card_eq_fintypeCard]
  exact Finset.card_le_univ _

theorem baseSupport_subset (candidate : profile.Candidate) :
    profile.baseSupport ⊆ profile.carrierSupport candidate := by
  intro carrier member
  simp [carrierSupport, member]

theorem itemSupport_subset (candidate : profile.Candidate) {item : Item}
    (selected : item ∈ candidate.1) :
    profile.itemSupport item ⊆ profile.carrierSupport candidate := by
  intro carrier member
  letI : DecidableEq Carrier := profile.carrierDecidableEq
  letI : DecidableEq Item := profile.items.decEq
  simp only [carrierSupport, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨item, selected, member⟩

/-- The complete declared item set.  This is a linear list-to-finset view of
the explicit local universe, not a subset enumeration. -/
def allItems : Finset Item := by
  letI : DecidableEq Item := profile.items.decEq
  exact profile.items.orderedValues.toFinset

@[simp]
theorem mem_allItems (item : Item) : item ∈ profile.allItems := by
  letI : DecidableEq Item := profile.items.decEq
  simp [allItems]

/-- The complete declared carrier universe of the demand, formed linearly
from the explicit item enumeration.  This is not a powerset scan. -/
def declaredCarrierSupport : Finset Carrier := by
  letI : DecidableEq Carrier := profile.carrierDecidableEq
  letI : DecidableEq Item := profile.items.decEq
  exact profile.baseSupport ∪ profile.allItems.biUnion profile.itemSupport

theorem mem_declaredCarrierSupport_iff (carrier : Carrier) :
    carrier ∈ profile.declaredCarrierSupport ↔
      carrier ∈ profile.baseSupport ∨
        ∃ item, carrier ∈ profile.itemSupport item := by
  letI : DecidableEq Carrier := profile.carrierDecidableEq
  letI : DecidableEq Item := profile.items.decEq
  simp [declaredCarrierSupport]

/-- Universe-lifting a local item type does not change its declared carrier
universe. -/
theorem mem_uliftItems_declaredCarrierSupport_iff (carrier : Carrier) :
    carrier ∈ profile.uliftItems.declaredCarrierSupport ↔
      carrier ∈ profile.declaredCarrierSupport := by
  rw [profile.uliftItems.mem_declaredCarrierSupport_iff,
    profile.mem_declaredCarrierSupport_iff]
  simp [uliftItems]

/-- Transport any carrier property through an item-universe lift without
unfolding the lifted finite profile at the application site. -/
theorem uliftItems_declaredCarrierSupport_of
    (Property : Carrier → Prop)
    (original : ∀ carrier,
      carrier ∈ profile.declaredCarrierSupport → Property carrier)
    {carrier : Carrier}
    (member : carrier ∈ profile.uliftItems.declaredCarrierSupport) :
    Property carrier :=
  original carrier
    ((profile.mem_uliftItems_declaredCarrierSupport_iff carrier).1 member)

theorem baseSupport_subset_declared :
    profile.baseSupport ⊆ profile.declaredCarrierSupport := by
  intro carrier member
  simp [declaredCarrierSupport, member]

/-- Prove a property of every declared carrier by checking the fixed base
support and each literal item's support.  This is a linear elimination rule
for the declared universe and performs no candidate-subset search. -/
theorem declaredCarrierSupport_induction
    (Property : Carrier → Prop)
    (base : ∀ carrier, carrier ∈ profile.baseSupport → Property carrier)
    (item : ∀ selected carrier,
      carrier ∈ profile.itemSupport selected → Property carrier)
    {carrier : Carrier}
    (member : carrier ∈ profile.declaredCarrierSupport) :
    Property carrier := by
  letI : DecidableEq Carrier := profile.carrierDecidableEq
  letI : DecidableEq Item := profile.items.decEq
  simp only [declaredCarrierSupport, Finset.mem_union,
    Finset.mem_biUnion] at member
  rcases member with baseMember | ⟨selected, _selectedMember, itemMember⟩
  · exact base carrier baseMember
  · exact item selected carrier itemMember

/-- Every valid selection is supported inside the declared carrier universe,
even when the valid candidate fibre itself is empty. -/
theorem carrierSupport_subset_declared (candidate : profile.Candidate) :
    profile.carrierSupport candidate ⊆ profile.declaredCarrierSupport := by
  intro carrier member
  letI : DecidableEq Carrier := profile.carrierDecidableEq
  letI : DecidableEq Item := profile.items.decEq
  simp only [carrierSupport, declaredCarrierSupport, Finset.mem_union,
    Finset.mem_biUnion] at member ⊢
  rcases member with base | ⟨item, selected, supported⟩
  · exact Or.inl base
  · exact Or.inr ⟨item, profile.mem_allItems item, supported⟩

/-- When no item is forbidden and the total declared weight pays the demand,
the all-items candidate exists constructively. -/
def allItemsCandidate
    (allowed : ∀ item, ¬profile.forbidden item)
    (pays : profile.required ≤
      ∑ item ∈ profile.allItems, profile.weight item) :
    profile.Candidate := by
  refine ⟨profile.allItems, ?_⟩
  refine ⟨?_, ?_, pays⟩
  · intro item _mandatory
    exact profile.mem_allItems item
  · intro item _selected
    exact allowed item

/-- The candidate fibre is finite because it is a subtype of finite subsets
of the declared item universe.  This theorem exposes the logical fact without
constructing a powerset table. -/
theorem finite_candidate_fibre : Finite profile.Candidate := inferInstance

end Profile

end StructuralExhaustion.Core.FiniteWeightedSelection
