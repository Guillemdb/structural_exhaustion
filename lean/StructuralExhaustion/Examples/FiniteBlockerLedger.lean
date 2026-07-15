import StructuralExhaustion.Core.FiniteBlockerLedger

namespace StructuralExhaustion.Examples.FiniteBlockerLedger

open StructuralExhaustion

def candidates : Core.OrderedCollection Nat where
  values := [1, 2, 3, 4]
  nodup := by decide
  decEq := inferInstance

def profile : Core.FiniteBlockerLedger.Profile Nat Nat where
  candidates := fun _pair ↦ candidates
  Blocks := fun pair candidate ↦ pair ∣ candidate
  blocksDecidable := fun _ _ ↦ inferInstance

def result := profile.run 2

example : result.value? = some 2 := rfl

example : profile.checks 2 = 4 := rfl

example :
    (∃ hit, profile.run 2 = .found hit) ∨
      (∃ none, profile.run 2 = .absent none) :=
  profile.stateSpace 2

@[implicit_reducible]
def pairEnumeration : FinEnum (Fin 3) := inferInstance

def familyProfile : Core.FiniteBlockerLedger.FamilyProfile (Fin 3) Nat where
  pairs := pairEnumeration
  scan := {
    candidates := fun _pair ↦ candidates
    Blocks := fun pair candidate ↦ pair.1 + 1 ∣ candidate
    blocksDecidable := fun _ _ ↦ inferInstance
  }

def blockedOne : {pair : Fin 3 // familyProfile.HasBlocker pair} :=
  ⟨1, ⟨2, by decide, by
    change 2 ∣ 2
    exact dvd_refl 2⟩⟩

example : (familyProfile.firstBlocker blockedOne).value = 2 := rfl

example :
    familyProfile.blockedPairs.card + familyProfile.freePairs.card =
      familyProfile.pairs.card :=
  familyProfile.blocked_card_add_free_card

example :
    familyProfile.scan.Blocks blockedOne.1
      (familyProfile.firstBlocker blockedOne).value :=
  (familyProfile.firstBlocker_sound blockedOne).2.1

end StructuralExhaustion.Examples.FiniteBlockerLedger
