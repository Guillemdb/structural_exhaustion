import Erdos64EG.CT3
import StructuralExhaustion.CT4.Cardinality

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u uEntry uCarrier

/-!
# Part IX route-8 private-carrier accounting

This is the thin Erdős specialization of the framework-owned CT4 private-
carrier capacity pattern used at manuscript nodes `[119]`--`[120]`.  It does
not create the route-8 entries or their canonical carrier cores: those are the
graph-semantic outputs required from nodes `[110]`--`[114]`.
-/

structure P13Route8PrivateCarrierLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  Entry : Type uEntry
  Carrier : Type uCarrier
  entries : FinEnum Entry
  carriers : FinEnum Carrier
  Private : Entry → Carrier → Prop
  chosen : Entry → Fin 3 → Carrier
  chosen_private : ∀ entry slot, Private entry (chosen entry slot)
  chosen_distinct : ∀ entry, Function.Injective (chosen entry)
  private_owner : ∀ carrier left right,
    Private left carrier → Private right carrier → left = right

namespace P13Route8PrivateCarrierLedger

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (ledger : P13Route8PrivateCarrierLedger ctx)

@[implicit_reducible]
def slots : FinEnum (Fin 3) := inferInstance

noncomputable def ct4Profile : CT4.PrivateCarrierProfile PackedProblem where
  Entry := ledger.Entry
  Carrier := ledger.Carrier
  Slot := Fin 3
  entries := ledger.entries
  carriers := ledger.carriers
  slots := slots
  Private := fun _input entry carrier => ledger.Private entry carrier
  chosen := fun _input entry slot => ledger.chosen entry slot
  chosen_private := fun _input => ledger.chosen_private
  chosen_distinct := fun _input => ledger.chosen_distinct
  private_owner := fun _input => ledger.private_owner

/-- Manuscript node `[120]`'s no-overcounting inequality before identifying
the carrier ledger with oriented boundary incidences. -/
theorem three_mul_entries_le_carriers :
    3 * ledger.entries.card ≤ ledger.carriers.card := by
  have bound := (ledger.ct4Profile.slot_mul_entry_le_carrier ctx.toBranchContext)
  change ledger.entries.card * (slots : FinEnum (Fin 3)).card ≤
    ledger.carriers.card at bound
  simpa [slots, Nat.mul_comm] using bound

/-- Ledger transport and CT4's capacity theorem add no local scan. -/
def localCheckCount (_ledger : P13Route8PrivateCarrierLedger ctx) : Nat := 0

theorem localCheckCount_polynomial :
    ledger.localCheckCount ≤
      (ledger.entries.card + ledger.carriers.card + 1) ^ 1 := by
  simp [localCheckCount]

end P13Route8PrivateCarrierLedger

end Erdos64EG.Internal
