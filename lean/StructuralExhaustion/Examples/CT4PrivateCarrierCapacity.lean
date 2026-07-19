import StructuralExhaustion.CT4.Cardinality

namespace StructuralExhaustion.Examples.CT4PrivateCarrierCapacity

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def input : CT4.Input problem where
  G := ()
  baseline := trivial
  state := ()

@[implicit_reducible] def entries : FinEnum Bool := Core.Enumeration.bool
@[implicit_reducible] def slots : FinEnum (Fin 2) := inferInstance
@[implicit_reducible] def carriers : FinEnum (Bool × Fin 2) :=
  Core.Enumeration.prod entries slots

def profile : CT4.PrivateCarrierProfile problem where
  Entry := Bool
  Carrier := Bool × Fin 2
  Slot := Fin 2
  entries := entries
  carriers := carriers
  slots := slots
  Private := fun _ entry carrier => carrier.1 = entry
  chosen := fun _ entry slot => (entry, slot)
  chosen_private := by simp
  chosen_distinct := by
    intro _input entry left right equal
    exact congrArg Prod.snd equal
  private_owner := by
    intro _input carrier left right leftPrivate rightPrivate
    exact leftPrivate.symm.trans rightPrivate

example : entries.card * slots.card ≤ carriers.card :=
  profile.slot_mul_entry_le_carrier input

example : profile.localCheckCount input = 0 := rfl

end StructuralExhaustion.Examples.CT4PrivateCarrierCapacity
