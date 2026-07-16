import StructuralExhaustion.Core.FiniteBoundedOverlap
import StructuralExhaustion.Core.FiniteFirstFailure
import Mathlib.Tactic

namespace StructuralExhaustion.Examples.FiniteColdGermLedger

open StructuralExhaustion

/-! A non-graph transfer fixture for the reusable cold-ledger primitives. -/

def stages : Core.OrderedCollection (Fin 3) :=
  (inferInstance : FinEnum (Fin 3)).toOrderedCollection

def firstFailure : Core.FiniteFirstFailure.Profile Unit (Fin 3) where
  corridors := Core.Enumeration.unit
  stages := fun _ ↦ stages
  F1 := fun _ stage ↦ stage.1 = 1
  F2 := fun _ _ ↦ False
  F3 := fun _ _ ↦ False
  F4 := fun _ _ ↦ False
  f1Decidable := fun _ _ ↦ inferInstance
  f2Decidable := fun _ _ ↦ .isFalse id
  f3Decidable := fun _ _ ↦ .isFalse id
  f4Decidable := fun _ _ ↦ .isFalse id
  F1Data := Nat
  F2Data := PEmpty
  F3Data := PEmpty
  F4Data := PEmpty
  f1Data := fun _ stage _ ↦ stage.1
  f2Data := fun _ _ impossible ↦ impossible.elim
  f3Data := fun _ _ impossible ↦ impossible.elim
  f4Data := fun _ _ impossible ↦ impossible.elim
  Germ := fun _ ↦ Unit
  germOfClear := fun _ _ ↦ ()

theorem firstFailure_is_first_stage_one :
    ∃ hit data, firstFailure.run () = .first hit data ∧ hit.value.1 = 1 := by
  cases equation : firstFailure.run () with
  | first hit data =>
      refine ⟨hit, data, rfl, ?_⟩
      simpa [Core.FiniteFirstFailure.Profile.Event, firstFailure] using hit.holds
  | germ noEvent data =>
      have member : (⟨1, by decide⟩ : Fin 3) ∈ stages.values := by decide
      have event : firstFailure.Event () ⟨1, by decide⟩ := by
        simp [Core.FiniteFirstFailure.Profile.Event, firstFailure]
      exact (noEvent _ member event).elim

def support (item : Fin 4) : Finset (Fin 2) :=
  {⟨item.1 % 2, Nat.mod_lt _ (by decide)⟩}

def packingProfile : Core.FiniteDisjointPacking.Profile (Fin 2) (Fin 4) where
  vertices := inferInstance
  finiteItems := inferInstance
  support := support
  representative := fun item ↦ ⟨item.1 % 2, Nat.mod_lt _ (by decide)⟩
  representative_mem := fun item ↦ by simp [support]

def overlapProfile : Core.FiniteBoundedOverlap.Profile (Fin 2) (Fin 4) where
  packing := packingProfile
  overlapBound := 4
  overlap_bounded := by
    intro selected
    letI : Fintype (Fin 4) := Fintype.ofFinite (Fin 4)
    let all : Finset (Fin 4) := {0, 1, 2, 3}
    calc
      ((Finset.univ : Finset (Fin 4)).filter fun item ↦
          ¬Disjoint (support item) (support selected)).card ≤ all.card := by
        apply Finset.card_le_card
        intro item _
        change item ∈ ({0, 1, 2, 3} : Finset (Fin 4))
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have cases : item.1 = 0 ∨ item.1 = 1 ∨ item.1 = 2 ∨
            item.1 = 3 := by omega
        rcases cases with zero | one | two | three
        · exact Or.inl (Fin.ext zero)
        · exact Or.inr (Or.inl (Fin.ext one))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext two)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext three)))
      _ = 4 := by decide

theorem four_items_paid_by_two_overlap_fibres :
    overlapProfile.itemCount ≤
      overlapProfile.selected.card * overlapProfile.overlapBound :=
  overlapProfile.card_le_selected_mul_overlapBound

theorem selected_supports_disjoint :
    (overlapProfile.selected : Set (Fin 4)).PairwiseDisjoint support :=
  overlapProfile.selected_pairwise

end StructuralExhaustion.Examples.FiniteColdGermLedger
