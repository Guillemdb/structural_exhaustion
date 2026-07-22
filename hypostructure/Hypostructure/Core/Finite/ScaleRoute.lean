import Hypostructure.Core.Finite.Search
import Hypostructure.Core.Residual.Decision
import Hypostructure.Core.Residual.Focus

/-!
# Generic finite scale routing

This module owns the bounded-vs-long split for a local finite object.  The
problem contract supplies the measured support size and the selected scale;
Core performs the comparison and exposes the two residual predicates.
-/

namespace Hypostructure.Core.Finite.ScaleRoute

open Hypostructure.Core.Residual

universe uPrevious u

/-- Public scale-routing contract for one item. -/
structure Contract (Item : Type u) where
  supportSize : Item -> Nat
  scale : Item -> Nat

namespace Contract

variable {Item : Type u} (contract : Contract Item)

def Bounded (item : Item) : Prop :=
  contract.supportSize item <= contract.scale item

def Long (item : Item) : Prop :=
  contract.scale item < contract.supportSize item

/-- Core-owned exhaustive scale decision. -/
def decision (_item : Item) :
    Decision.Node Item contract.Bounded contract.Long :=
  Decision.Node.create
    (fun item => by
      by_cases h : contract.supportSize item <= contract.scale item
      · exact Decidable.isTrue h
      · exact Decidable.isFalse h)
    (fun _item notBounded => Nat.lt_of_not_ge notBounded)

def run (item : Item) : Decision.Stage contract.Bounded contract.Long :=
  (contract.decision item).run item

theorem run_checks (item : Item) :
    ((contract.decision item).runCounted item).checks = 1 :=
  Decision.Node.runCounted_checks (contract.decision item) item

/-- If the problem contract proves every long item impossible, the route
returns the bounded residual. -/
theorem bounded_of_long_impossible (item : Item)
    (longImpossible : Not (contract.Long item)) :
    contract.Bounded item := by
  by_cases bounded : contract.Bounded item
  · exact bounded
  · exact (longImpossible (Nat.lt_of_not_ge bounded)).elim

end Contract

/-! ## Focused residual executor -/

/-- Residual-owned scale-routing contract for one active item.  The active
residual supplies the item, support size, and scale through ledger queries;
Core owns the bounded-vs-long comparison and successor routing. -/
structure FocusedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type u
  item : Focus.ActiveQuery focus fun _previous _active => Item
  supportSize : Focus.ActiveQuery focus fun _previous _active => Nat
  scale : Focus.ActiveQuery focus fun _previous _active => Nat

namespace FocusedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedContract focus)

/-- Bounded residual predicate at an active predecessor. -/
def Bounded (previous : Previous) (active : focus.Active previous) : Prop :=
  contract.supportSize.read previous active <= contract.scale.read previous active

/-- Long residual predicate at an active predecessor. -/
def Long (previous : Previous) (active : focus.Active previous) : Prop :=
  contract.scale.read previous active < contract.supportSize.read previous active

/-- Core-owned route certificate for one active predecessor. -/
inductive Certificate (previous : Previous)
    (active : focus.Active previous) : Type where
  | bounded : contract.Bounded previous active ->
      Certificate previous active
  | long : contract.Long previous active ->
      Certificate previous active

/-- Focused stage carrying exactly one scale-route certificate. -/
abbrev Stage :=
  Focus.Stage focus fun previous active =>
    contract.Certificate previous active

/-- Execute the bounded-vs-long comparison and register the selected
certificate. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCountedPayload focus
    (PolynomialCheckBudget.constant (fun _previous => 0) 1) previous
    (fun active _checks _exact =>
      if bounded :
          contract.supportSize.read previous active <=
            contract.scale.read previous active then
        { value := Certificate.bounded bounded
          checks := 1 }
      else
        { value := Certificate.long (Nat.lt_of_not_ge bounded)
          checks := 1 })
    (fun _active _checks _exact => by
      by_cases bounded :
          contract.supportSize.read previous _active <=
            contract.scale.read previous _active <;>
        simp [bounded, PolynomialCheckBudget.constant])

/-- Uncounted public executor. -/
def execute (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

/-- Public CT-style executor spelling. -/
abbrev runStage (previous : Previous) : contract.Stage :=
  contract.execute previous

@[simp] theorem execute_previous (previous : Previous) :
    (contract.execute previous).previous = previous :=
  Focus.runCountedPayload_previous focus
    (PolynomialCheckBudget.constant (fun _previous => 0) 1) previous _ _

@[simp] theorem runStage_previous (previous : Previous) :
    (contract.runStage previous).previous = previous :=
  contract.execute_previous previous

theorem executeCounted_checks_of_active (previous : Previous)
    (active : focus.Active previous) :
    (contract.executeCounted previous).checks =
      (focus.selectionBudget.add
        (PolynomialCheckBudget.constant (fun _previous => 0) 1)).checks
        previous :=
  Focus.runCountedPayload_checks_of_active focus
    (PolynomialCheckBudget.constant (fun _previous => 0) 1) previous _ _
    active

abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor focus fun previous active =>
    contract.Certificate previous active

/-- Read the latest scale-route certificate. -/
def latestCertificate :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.Certificate stage.previous active :=
  Focus.ActiveQuery.latest

/-- Focus on the bounded branch. -/
def boundedRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ bounded : contract.Bounded stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.bounded bounded)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | bounded bounded => exact isTrue ⟨bounded, rfl⟩
      | long _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨bounded, equal⟩
            cases equal)))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

/-- Focus on the long branch. -/
def longRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ long : contract.Long stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.long long)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | bounded _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨long, equal⟩
            cases equal)
      | long long => exact isTrue ⟨long, rfl⟩))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

/-- Live focus containing exactly the bounded branch. -/
abbrev boundedFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.boundedRefinement

/-- Live focus containing exactly the long branch. -/
abbrev longFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.longRefinement

/-- Read the bounded proof selected by Core. -/
def boundedQuery :
    Focus.ActiveQuery contract.boundedFocus fun stage active =>
      contract.Bounded stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

/-- Read the long proof selected by Core. -/
def longQuery :
    Focus.ActiveQuery contract.longFocus fun stage active =>
      contract.Long stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

/-- If the long branch is impossible in the problem contract, recover the
bounded residual without rerouting outside Core. -/
theorem bounded_of_long_impossible (previous : Previous)
    (active : focus.Active previous)
    (longImpossible : Not (contract.Long previous active)) :
    contract.Bounded previous active := by
  by_cases bounded : contract.Bounded previous active
  · exact bounded
  · exact (longImpossible (Nat.lt_of_not_ge bounded)).elim

end FocusedContract

/-! ## Focused schedule executor -/

/-- Residual-owned schedule-wide scale routing.  Core scans the exact active
schedule for the first long item; if none exists, it registers a pointwise
bounded residual for every scheduled item. -/
structure FocusedScheduleContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type u
  schedule : Focus.ActiveQuery focus fun _previous _active =>
    Hypostructure.Core.Finite.Enumeration Item
  supportSize : (previous : Previous) -> focus.Active previous -> Item -> Nat
  scale : (previous : Previous) -> focus.Active previous -> Item -> Nat

namespace FocusedScheduleContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedScheduleContract focus)

def Bounded (previous : Previous) (active : focus.Active previous)
    (item : contract.Item) : Prop :=
  contract.supportSize previous active item <= contract.scale previous active item

def Long (previous : Previous) (active : focus.Active previous)
    (item : contract.Item) : Prop :=
  contract.scale previous active item < contract.supportSize previous active item

def AnyLong (previous : Previous) (active : focus.Active previous) : Prop :=
  ∃ item ∈ (contract.schedule.read previous active).values,
    contract.Long previous active item

def AllBounded (previous : Previous) (active : focus.Active previous) : Prop :=
  ∀ item ∈ (contract.schedule.read previous active).values,
    contract.Bounded previous active item

inductive Certificate (previous : Previous)
    (active : focus.Active previous) : Type where
  | long : contract.AnyLong previous active ->
      Certificate previous active
  | allBounded : contract.AllBounded previous active ->
      Certificate previous active

abbrev Stage :=
  Focus.Stage focus fun previous active =>
    contract.Certificate previous active

def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    let schedule := contract.schedule.read previous active
    let execution :=
      Search.run schedule (contract.Long previous active)
        (fun item => by
          unfold Long
          infer_instance)
    match found : execution.hit? with
    | some hit =>
        Certificate.long ⟨hit.value, hit.member, hit.sound⟩
    | none =>
        Certificate.allBounded (by
          intro item member
          rcases (schedule.mem_iff_exists_index item).mp member with
            ⟨index, rfl⟩
          have notLong := execution.exhaustive found index
          exact Nat.le_of_not_gt notLong)

def execute (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

abbrev runStage (previous : Previous) : contract.Stage :=
  contract.execute previous

@[simp] theorem execute_previous (previous : Previous) :
    (contract.execute previous).previous = previous :=
  Focus.runCounted_previous focus previous _

@[simp] theorem runStage_previous (previous : Previous) :
    (contract.runStage previous).previous = previous :=
  contract.execute_previous previous

theorem executeCounted_checks (previous : Previous) :
    (contract.executeCounted previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor focus fun previous active =>
    contract.Certificate previous active

def latestCertificate :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.Certificate stage.previous active :=
  Focus.ActiveQuery.latest

def longRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ long : contract.AnyLong stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.long long)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | long long => exact isTrue ⟨long, rfl⟩
      | allBounded _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨long, equal⟩
            cases equal)))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

def allBoundedRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ allBounded : contract.AllBounded stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.allBounded allBounded)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | long _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨allBounded, equal⟩
            cases equal)
      | allBounded allBounded => exact isTrue ⟨allBounded, rfl⟩))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

abbrev longFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.longRefinement

abbrev allBoundedFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.allBoundedRefinement

def longQuery :
    Focus.ActiveQuery contract.longFocus fun stage active =>
      contract.AnyLong stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

def allBoundedQuery :
    Focus.ActiveQuery contract.allBoundedFocus fun stage active =>
      contract.AllBounded stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

end FocusedScheduleContract

end Hypostructure.Core.Finite.ScaleRoute
