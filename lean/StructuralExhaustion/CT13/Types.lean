import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT13

universe uPayer uObstruction uResource

structure Capability (P : Core.Problem) where
  Payer : Type uPayer
  payers : FinEnum Payer
  Eligible : Core.BranchContext P → Payer → Prop
  eligibleDecidable : ∀ ctx payer, Decidable (Eligible ctx payer)
  Obstruction : Type uObstruction
  obstructions : FinEnum Obstruction
  fallbackDefault : Obstruction
  obstructionCost : Core.BranchContext P → Obstruction → Nat
  Resource : Type uResource
  resourceDecidableEq : DecidableEq Resource
  resource : Core.BranchContext P → Payer → Resource
  tierTwo : Core.BranchContext P → Obstruction → Core.OrderedCollection Payer
  charge : Core.BranchContext P → Payer → Nat
  demand : Core.BranchContext P → Nat

structure Input {P : Core.Problem} (_C : Capability P)
    (_ctx : Core.BranchContext P) where
namespace Capability
def tacticInterface {P : Core.Problem} (C : Capability P) :
    Core.Routing.TacticInterface where
  Context := Core.BranchContext P; Trigger := Input C
end Capability

structure TierOneResidual {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  payer : C.Payer
  eligible : C.Eligible ctx payer

def selectMin {α : Type u} (cost : α → Nat) : α → List α → α
  | current, [] => current
  | current, head :: tail =>
      selectMin cost (if cost head < cost current then head else current) tail

theorem selectMin_le_current {α : Type u} (cost : α → Nat)
    (current : α) (values : List α) :
    cost (selectMin cost current values) ≤ cost current := by
  induction values generalizing current with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      unfold selectMin
      by_cases lower : cost head < cost current
      · simp only [if_pos lower]
        exact Nat.le_trans (ih head) (Nat.le_of_lt lower)
      · simp only [if_neg lower]
        exact ih current

theorem selectMin_le_of_mem {α : Type u} (cost : α → Nat)
    (current value : α) (values : List α) (member : value ∈ values) :
    cost (selectMin cost current values) ≤ cost value := by
  induction values generalizing current with
  | nil => cases member
  | cons head tail ih =>
      unfold selectMin
      simp only [List.mem_cons] at member
      by_cases lower : cost head < cost current
      · simp only [if_pos lower]
        cases member with
        | inl equal => subst value; exact selectMin_le_current cost head tail
        | inr inTail => exact ih head inTail
      · simp only [if_neg lower]
        cases member with
        | inl equal =>
            subst value
            exact Nat.le_trans (selectMin_le_current cost current tail)
              (Nat.le_of_not_gt lower)
        | inr inTail => exact ih current inTail

structure TierOneAbsenceState {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : Prop where
  absent : ∀ payer, ¬ C.Eligible ctx payer

/-- Canonical fallback computed only after exhaustive tier-one absence. -/
structure FallbackState {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  tierOneAbsent : TierOneAbsenceState C ctx
  selected : C.Obstruction
  canonical : selected = selectMin (C.obstructionCost ctx)
    C.fallbackDefault C.obstructions.orderedValues
  minimal : ∀ obstruction,
    C.obstructionCost ctx selected ≤ C.obstructionCost ctx obstruction

def totalCharge {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (obstruction : C.Obstruction) : Nat :=
  ((C.tierTwo ctx obstruction).values.map (C.charge ctx)).sum

structure OverlapResidual {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  fallback : FallbackState C ctx
  left : C.Payer
  right : C.Payer
  different : left ≠ right
  sameResource : C.resource ctx left = C.resource ctx right

structure ReconciledState {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  fallback : FallbackState C ctx
  capacity : Nat
  exact : capacity = totalCharge C ctx fallback.selected

inductive ReconciliationDecision {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  | overlap (residual : OverlapResidual C ctx)
  | clean (state : ReconciledState C ctx)

private def sameResourceDecidable {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (left right : C.Payer) :
    Decidable (C.resource ctx left = C.resource ctx right) :=
  C.resourceDecidableEq _ _

private def reconcileList {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (fallback : FallbackState C ctx) :
    (values : List C.Payer) → values.Nodup → ReconciliationDecision C ctx
  | [], _ => .clean ⟨fallback, totalCharge C ctx fallback.selected, rfl⟩
  | head :: tail, nodup =>
      match Core.FiniteSearch.onList tail
          (fun other => C.resource ctx head = C.resource ctx other)
          (sameResourceDecidable C ctx head) with
      | .found other member same => .overlap ⟨fallback, head, other,
          fun equal => (List.nodup_cons.mp nodup).1 (equal ▸ member), same⟩
      | .absent _ => reconcileList C ctx fallback tail (List.nodup_cons.mp nodup).2

def reconcile {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (fallback : FallbackState C ctx) :
    ReconciliationDecision C ctx :=
  reconcileList C ctx fallback (C.tierTwo ctx fallback.selected).values
    (C.tierTwo ctx fallback.selected).nodup

structure DeficitResidual {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  state : ReconciledState C ctx
  deficit : state.capacity < C.demand ctx

structure ReconciliationCertificate {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  state : ReconciledState C ctx
  covers : C.demand ctx ≤ state.capacity

inductive ComparisonDecision {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  | deficit (r : DeficitResidual C ctx)
  | covers (c : ReconciliationCertificate C ctx)

def compare {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (state : ReconciledState C ctx) : ComparisonDecision C ctx :=
  if h : state.capacity < C.demand ctx then .deficit ⟨state, h⟩
  else .covers ⟨state, Nat.le_of_not_gt h⟩

inductive TierOneDecision {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  | found (r : TierOneResidual C ctx)
  | absent (s : TierOneAbsenceState C ctx)

def selectTierOne {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : TierOneDecision C ctx :=
  match Core.FiniteSearch.first C.payers (C.Eligible ctx) (C.eligibleDecidable ctx) with
  | .found hit => .found ⟨hit.value, hit.holds⟩
  | .absent absent => .absent ⟨fun payer =>
      absent payer (C.payers.mem_orderedValues payer)⟩

/-- Deterministically compute the least-cost fallback after the search node has
certified that no tier-one payer exists. -/
def computeFallback {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (absence : TierOneAbsenceState C ctx) :
    FallbackState C ctx where
  tierOneAbsent := absence
  selected := selectMin (C.obstructionCost ctx)
    C.fallbackDefault C.obstructions.orderedValues
  canonical := rfl
  minimal := fun obstruction => selectMin_le_of_mem
    (C.obstructionCost ctx) C.fallbackDefault obstruction C.obstructions.orderedValues
    (C.obstructions.mem_orderedValues obstruction)

end StructuralExhaustion.CT13
