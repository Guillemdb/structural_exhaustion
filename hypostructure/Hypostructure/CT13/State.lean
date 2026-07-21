import Hypostructure.CT13.Capability
import Hypostructure.Core.Finite.Accounting

/-!
# CT13 generated fallback and reconciliation states

Every state is computed from schedules queried from the literal predecessor.
The fallback and reconciliation constructors are private so callers cannot
replace canonical framework computation with an authored representative.
-/

namespace Hypostructure.CT13

universe uPrevious uPayer uObstruction uResource

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uPayer, uObstruction, uResource} Previous}

/-- Seed-retaining minimum selection.  Because the seed is the first member
of `ObstructionSchedule`, this is stable first-minimum tie-breaking. -/
def selectMin {alpha : Type uObstruction} (cost : alpha -> Nat) :
    alpha -> List alpha -> alpha
  | current, [] => current
  | current, head :: tail =>
      selectMin cost (if cost head < cost current then head else current) tail

theorem selectMin_le_current {alpha : Type uObstruction} (cost : alpha -> Nat)
    (current : alpha) (values : List alpha) :
    cost (selectMin cost current values) <= cost current := by
  induction values generalizing current with
  | nil => exact Nat.le_refl _
  | cons head tail induction =>
      unfold selectMin
      by_cases lower : cost head < cost current
      · simp only [if_pos lower]
        exact Nat.le_trans (induction head) (Nat.le_of_lt lower)
      · simp only [if_neg lower]
        exact induction current

theorem selectMin_le_of_mem {alpha : Type uObstruction} (cost : alpha -> Nat)
    (current value : alpha) (values : List alpha)
    (member : value ∈ values) :
    cost (selectMin cost current values) <= cost value := by
  induction values generalizing current with
  | nil => cases member
  | cons head tail induction =>
      unfold selectMin
      simp only [List.mem_cons] at member
      by_cases lower : cost head < cost current
      · simp only [if_pos lower]
        cases member with
        | inl equal =>
            subst value
            exact selectMin_le_current cost head tail
        | inr inTail => exact induction head inTail
      · simp only [if_neg lower]
        cases member with
        | inl equal =>
            subst value
            exact Nat.le_trans (selectMin_le_current cost current tail)
              (Nat.le_of_not_gt lower)
        | inr inTail => exact induction current inTail

/-- Canonical selection remains in the seed-plus-tail schedule. -/
theorem selectMin_mem {alpha : Type uObstruction} (cost : alpha -> Nat)
    (current : alpha) (values : List alpha) :
    selectMin cost current values ∈ current :: values := by
  induction values generalizing current with
  | nil => simp [selectMin]
  | cons head tail induction =>
      by_cases lower : cost head < cost current
      · have selected := induction head
        simp only [selectMin, if_pos lower]
        simp only [List.mem_cons] at selected ⊢
        exact Or.inr selected
      · have selected := induction current
        simp only [selectMin, if_neg lower]
        simp only [List.mem_cons] at selected ⊢
        rcases selected with equal | inTail
        · exact Or.inl equal
        · exact Or.inr (Or.inr inTail)

/-- Canonical first eligible payer in the inherited tier-one order. -/
abbrev TierOneResidual (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.payersAt previous)
    (spec.Eligible previous)

/-- Exhaustive tier-one absence on the exact inherited payer order. -/
abbrev TierOneAbsenceState (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.payersAt previous)
    (spec.Eligible previous)

/-- Canonical minimum-cost fallback, generated only after exhaustive
tier-one absence. -/
structure FallbackState (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  tierOneAbsent : TierOneAbsenceState capability previous
  selected : spec.Obstruction previous
  selected_member :
    selected ∈ (capability.obstructionsAt previous).enumeration.values
  canonical : selected = selectMin (spec.obstructionCost previous)
    (capability.obstructionsAt previous).fallbackDefault
    (capability.obstructionsAt previous).remaining
  minimal : forall obstruction,
    obstruction ∈ (capability.obstructionsAt previous).enumeration.values ->
      spec.obstructionCost previous selected <=
        spec.obstructionCost previous obstruction

/-- Compute the unique first-minimum fallback from the inherited obstruction
order. -/
def computeFallback (capability : Capability spec) (previous : Previous)
    (absence : TierOneAbsenceState capability previous) :
    FallbackState capability previous := by
  let schedule := capability.obstructionsAt previous
  let selected := selectMin (spec.obstructionCost previous)
    schedule.fallbackDefault schedule.remaining
  refine .mk absence selected ?_ rfl ?_
  · exact selectMin_mem (spec.obstructionCost previous)
      schedule.fallbackDefault schedule.remaining
  · intro obstruction member
    change obstruction ∈ schedule.fallbackDefault :: schedule.remaining at member
    simp only [List.mem_cons] at member
    rcases member with equal | inRemaining
    · subst obstruction
      exact selectMin_le_current (spec.obstructionCost previous)
        schedule.fallbackDefault schedule.remaining
    · exact selectMin_le_of_mem (spec.obstructionCost previous)
        schedule.fallbackDefault obstruction schedule.remaining inRemaining

/-- Exact ordered tier-two schedule selected by the fallback. -/
def selectedTierTwo (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :
    Core.Finite.Enumeration (spec.Payer previous) :=
  capability.tierTwoAt previous fallback.selected

/-- Framework-derived ordered pair schedule used for overlap detection. -/
def reconciliationPairs (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :
    Core.Finite.Enumeration
      (spec.Payer previous × spec.Payer previous) :=
  (selectedTierTwo capability previous fallback).product
    (selectedTierTwo capability previous fallback)

/-- Two distinct tier-two payers claim the same resource. -/
def ResourceOverlap (previous : Previous)
    (pair : spec.Payer previous × spec.Payer previous) : Prop :=
  pair.1 ≠ pair.2 ∧
    spec.payerResource previous pair.1 = spec.payerResource previous pair.2

/-- Exhaustive absence of resource overlap on the derived pair schedule. -/
abbrev OverlapFreeState (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :=
  Core.Finite.Search.Avoids
    (reconciliationPairs capability previous fallback)
    (ResourceOverlap (spec := spec) previous)

/-- Canonical first resource overlap. -/
structure OverlapResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  fallback : FallbackState capability previous
  hit : Core.Finite.Search.IndexedHit
    (reconciliationPairs capability previous fallback)
    (ResourceOverlap (spec := spec) previous)

/-- Package the exact Core-selected overlap without exposing a constructor. -/
def overlapResidual (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous)
    (hit : Core.Finite.Search.IndexedHit
      (reconciliationPairs capability previous fallback)
      (ResourceOverlap (spec := spec) previous)) :
    OverlapResidual capability previous :=
  .mk fallback hit

namespace OverlapResidual

def left {capability : Capability spec} {previous : Previous}
    (residual : OverlapResidual capability previous) :
    spec.Payer previous :=
  residual.hit.value.1

def right {capability : Capability spec} {previous : Previous}
    (residual : OverlapResidual capability previous) :
    spec.Payer previous :=
  residual.hit.value.2

theorem different {capability : Capability spec} {previous : Previous}
    (residual : OverlapResidual capability previous) :
    residual.left ≠ residual.right :=
  residual.hit.sound.1

theorem sameResource {capability : Capability spec} {previous : Previous}
    (residual : OverlapResidual capability previous) :
    spec.payerResource previous residual.left =
      spec.payerResource previous residual.right :=
  residual.hit.sound.2

end OverlapResidual

/-- Ordered reconciliation entries derived from the selected tier-two
schedule. -/
def reconciliationEntries (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) :
    List (spec.Payer previous × spec.Resource previous × Nat) :=
  (selectedTierTwo capability previous fallback).values.map fun payer =>
    (payer, spec.payerResource previous payer, spec.charge previous payer)

/-- Exact total charge in the selected tier-two schedule. -/
def totalCharge (capability : Capability spec) (previous : Previous)
    (fallback : FallbackState capability previous) : Nat :=
  (selectedTierTwo capability previous fallback).values.map
    (spec.charge previous) |>.sum

/-- Complete framework-generated reconciliation ledger. -/
structure ReconciliationLedger (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  fallback : FallbackState capability previous
  overlapFree : OverlapFreeState capability previous fallback
  entries : List (spec.Payer previous × spec.Resource previous × Nat)
  entries_exact : entries = reconciliationEntries capability previous fallback
  capacity : Nat
  capacity_exact : capacity = totalCharge capability previous fallback

/-- Build the unique ledger after exhaustive overlap exclusion. -/
def buildReconciliationLedger (capability : Capability spec)
    (previous : Previous) (fallback : FallbackState capability previous)
    (overlapFree : OverlapFreeState capability previous fallback) :
    ReconciliationLedger capability previous :=
  .mk fallback overlapFree
    (reconciliationEntries capability previous fallback) rfl
    (totalCharge capability previous fallback) rfl

/-- Remaining charge deficit after clean reconciliation. -/
structure DeficitResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  ledger : ReconciliationLedger capability previous
  deficit : ledger.capacity < spec.demand previous

/-- Reconciled tier-two resources cover the required demand. -/
structure ReconciliationCertificate (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  ledger : ReconciliationLedger capability previous
  covers : spec.demand previous <= ledger.capacity

/-- Package the exact generated ledger with the Core-selected deficit proof. -/
def deficitResidual (capability : Capability spec) (previous : Previous)
    (ledger : ReconciliationLedger capability previous)
    (deficit : ledger.capacity < spec.demand previous) :
    DeficitResidual capability previous :=
  .mk ledger deficit

/-- Package the exact generated ledger with the Core-selected coverage proof. -/
def reconciliationCertificate (capability : Capability spec)
    (previous : Previous)
    (ledger : ReconciliationLedger capability previous)
    (covers : spec.demand previous <= ledger.capacity) :
    ReconciliationCertificate capability previous :=
  .mk ledger covers

/-- The selected tier-two schedule is bounded by the sum over all inherited
obstruction schedules. -/
theorem selectedTierTwo_card_le_sum (capability : Capability spec)
    (previous : Previous) (fallback : FallbackState capability previous) :
    (selectedTierTwo capability previous fallback).card <=
      capability.tierTwoCardSumAt previous := by
  unfold Capability.tierTwoCardSumAt tierTwoCardSum selectedTierTwo
  generalize valuesEq :
      (capability.obstructionsAt previous).enumeration.values = values
  have selectedMember : fallback.selected ∈ values := by
    rw [← valuesEq]
    exact fallback.selected_member
  clear valuesEq
  induction values with
  | nil => cases selectedMember
  | cons head tail induction =>
      simp only [List.mem_cons] at selectedMember
      simp only [List.map_cons, List.sum_cons]
      rcases selectedMember with equal | inTail
      · subst head
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (induction inTail) (Nat.le_add_left _ _)

end Hypostructure.CT13
