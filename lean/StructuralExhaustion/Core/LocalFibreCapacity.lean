import Mathlib

namespace StructuralExhaustion.Core.LocalFibreCapacity

universe uItem uOwner

/-! A bounded-fibre count over two supplied finite lists. -/

structure Profile (Item : Type uItem) (Owner : Type uOwner) where
  items : List Item
  itemsNodup : items.Nodup
  owners : List Owner
  ownersNodup : owners.Nodup
  owner : Item → Owner
  sameOwner : Owner → Owner → Bool
  sameOwner_true : ∀ left right, sameOwner left right = true ↔ left = right
  owner_mem : ∀ item ∈ items, owner item ∈ owners

namespace Profile

variable {Item : Type uItem} {Owner : Type uOwner}
variable (profile : Profile Item Owner)

def fibre (owner : Owner) : List Item :=
  profile.items.filter fun item => profile.sameOwner (profile.owner item) owner

theorem fibre_nodup (owner : Owner) : (profile.fibre owner).Nodup :=
  profile.itemsNodup.filter _

theorem items_length_le_mul_owners_length
    (capacity : Nat)
    (bounded : ∀ owner ∈ profile.owners,
      (profile.fibre owner).length ≤ capacity) :
    profile.items.length ≤ capacity * profile.owners.length := by
  classical
  let itemsFinset := profile.items.toFinset
  let ownersFinset := profile.owners.toFinset
  have mapsTo : (itemsFinset : Set Item).MapsTo profile.owner ownersFinset := by
    intro item member
    change item ∈ itemsFinset at member
    change profile.owner item ∈ ownersFinset
    rw [List.mem_toFinset] at member ⊢
    exact profile.owner_mem item member
  have partition := Finset.card_eq_sum_card_fiberwise mapsTo
  rw [List.toFinset_card_of_nodup profile.itemsNodup] at partition
  calc
    profile.items.length =
        ∑ owner ∈ ownersFinset,
          (itemsFinset.filter fun item => profile.owner item = owner).card :=
      partition
    _ ≤ ∑ _owner ∈ ownersFinset, capacity := by
      apply Finset.sum_le_sum
      intro owner ownerMember
      have fibreCard :
          (itemsFinset.filter fun item => profile.owner item = owner).card =
            (profile.fibre owner).length := by
        rw [← List.toFinset_card_of_nodup (profile.fibre_nodup owner)]
        congr 1
        ext item
        simp [itemsFinset, fibre, profile.sameOwner_true]
      rw [fibreCard]
      apply bounded owner
      simpa [ownersFinset] using ownerMember
    _ = capacity * ownersFinset.card := by simp [Nat.mul_comm]
    _ = capacity * profile.owners.length := by
      rw [List.toFinset_card_of_nodup profile.ownersNodup]

end Profile

end StructuralExhaustion.Core.LocalFibreCapacity
