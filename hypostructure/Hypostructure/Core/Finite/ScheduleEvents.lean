import Hypostructure.Core.Finite.Search
import Hypostructure.Core.Residual.Focus

/-!
# Schedule-wide event execution

This module is the Core owner for repeated finite reductions over a
residual-owned schedule.  A problem contract supplies only the exact schedule,
an item runner, and event predicates on the runner output.  Core derives
pointwise totality, first-hit splitting, universal absence, and residual
refinement to a remaining outcome predicate.
-/

namespace Hypostructure.Core.Finite.ScheduleEvents

open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

universe uPrevious u v

/-- Minimal contract for a finite schedule of item-local executions. -/
structure Contract (Item : Type u) where
  schedule : Enumeration Item
  Output : Item -> Type v
  run : (item : Item) -> Output item

namespace Contract

variable {Item : Type u} (contract : Contract.{u, v} Item)

/-- A predicate holds for every scheduled item output. -/
def All (predicate : (item : Item) -> contract.Output item -> Prop) : Prop :=
  ∀ item ∈ contract.schedule.values, predicate item (contract.run item)

/-- Some scheduled item output satisfies the predicate. -/
def ExistsEvent (predicate : (item : Item) -> contract.Output item -> Prop) :
    Prop :=
  ∃ item ∈ contract.schedule.values, predicate item (contract.run item)

/-- No scheduled item output satisfies the predicate. -/
def NoEvent (predicate : (item : Item) -> contract.Output item -> Prop) :
    Prop :=
  Not (contract.ExistsEvent predicate)

/-- Exact first-hit execution for one event predicate. -/
def firstHit (predicate : (item : Item) -> contract.Output item -> Prop)
    (decidePredicate :
      (item : Item) -> Decidable (predicate item (contract.run item))) :
    Search.Execution contract.schedule
      (fun item => predicate item (contract.run item)) :=
  Search.run contract.schedule
    (fun item => predicate item (contract.run item)) decidePredicate

/-- A first-hit execution yields the event branch or the universal no-event
residual. -/
theorem firstHit_or_noEvent
    (predicate : (item : Item) -> contract.Output item -> Prop)
    (decidePredicate :
      (item : Item) -> Decidable (predicate item (contract.run item))) :
    contract.ExistsEvent predicate ∨ contract.NoEvent predicate := by
  classical
  cases found : (contract.firstHit predicate decidePredicate).hit? with
  | some hit =>
      exact Or.inl ⟨hit.value, hit.member, hit.sound⟩
  | none =>
      refine Or.inr ?_
      intro existsHit
      rcases existsHit with ⟨item, member, holds⟩
      rcases (contract.schedule.mem_iff_exists_index item).mp member with
        ⟨index, rfl⟩
      have avoids :=
        (contract.firstHit predicate decidePredicate).exhaustive found
      exact (avoids index) holds

/-- A universal no-event residual as a pointwise statement over scheduled
entries. -/
theorem pointwise_absent_of_noEvent
    (predicate : (item : Item) -> contract.Output item -> Prop)
    (noEvent : contract.NoEvent predicate) :
    ∀ item ∈ contract.schedule.values,
      Not (predicate item (contract.run item)) := by
  intro item member holds
  exact noEvent ⟨item, member, holds⟩

/-- Refine to a remaining outcome predicate once all excluded event predicates
are absent and every output is covered by the contract's totality law. -/
theorem all_remaining_of_totality
    (Excluded : (item : Item) -> contract.Output item -> Prop)
    (Remaining : (item : Item) -> contract.Output item -> Prop)
    (excludedAbsent : ∀ item ∈ contract.schedule.values,
      Not (Excluded item (contract.run item)))
    (totality : ∀ item ∈ contract.schedule.values,
      Excluded item (contract.run item) ∨
        Remaining item (contract.run item)) :
    contract.All Remaining := by
  intro item member
  cases totality item member with
  | inl excluded => exact (excludedAbsent item member excluded).elim
  | inr remaining => exact remaining

end Contract

/-! ## Focused residual executor -/

/-- Residual-owned schedule-event contract.  Consumers provide the active
schedule, item-local runner, event predicate, and predicate decider as ledger
queries.  Core owns the first-hit/no-event search and ledger registration. -/
structure FocusedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type u
  schedule : Focus.ActiveQuery focus fun _previous _active =>
    Enumeration Item
  Output : (previous : Previous) -> focus.Active previous -> Item -> Type v
  runner : Focus.ActiveQuery focus fun previous active =>
    (item : Item) -> Output previous active item
  event : (previous : Previous) -> (active : focus.Active previous) ->
    (item : Item) -> Output previous active item -> Prop
  eventDecidable : (previous : Previous) -> (active : focus.Active previous) ->
    (item : Item) ->
      Decidable (event previous active item
        ((runner.read previous active) item))

/-- Core constructor from active residual queries.  Domain layers should use
this helper instead of rebuilding schedule-event plumbing: they provide only
the exact residual-owned schedule, runner, event predicate, and decider. -/
def focusedFromQueries {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    (Item : Type u)
    (schedule : Focus.ActiveQuery focus fun _previous _active =>
      Enumeration Item)
    (Output : (previous : Previous) -> focus.Active previous -> Item ->
      Type v)
    (runner : Focus.ActiveQuery focus fun previous active =>
      (item : Item) -> Output previous active item)
    (event : (previous : Previous) -> (active : focus.Active previous) ->
      (item : Item) -> Output previous active item -> Prop)
    (eventDecidable :
      (previous : Previous) -> (active : focus.Active previous) ->
        (item : Item) ->
          Decidable (event previous active item
            ((runner.read previous active) item))) :
    FocusedContract focus where
  Item := Item
  schedule := schedule
  Output := Output
  runner := runner
  event := event
  eventDecidable := eventDecidable

namespace FocusedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedContract focus)

/-- Pure finite contract seen at one active predecessor. -/
def finiteContract (previous : Previous) (active : focus.Active previous) :
    Contract contract.Item where
  schedule := contract.schedule.read previous active
  Output := contract.Output previous active
  run := contract.runner.read previous active

/-- Event branch for the active predecessor. -/
def ExistsEvent (previous : Previous) (active : focus.Active previous) : Prop :=
  (contract.finiteContract previous active).ExistsEvent
    (contract.event previous active)

/-- Complementary no-event residual for the active predecessor. -/
def NoEvent (previous : Previous) (active : focus.Active previous) : Prop :=
  (contract.finiteContract previous active).NoEvent
    (contract.event previous active)

/-- Framework-owned event-search certificate. -/
inductive Certificate (previous : Previous)
    (active : focus.Active previous) : Type (max u v) where
  | hit : contract.ExistsEvent previous active ->
      Certificate previous active
  | noEvent : contract.NoEvent previous active ->
      Certificate previous active

/-- Focused stage carrying exactly one schedule-event certificate. -/
abbrev Stage :=
  Focus.Stage focus fun previous active =>
    contract.Certificate previous active

/-- Execute the schedule-event split and register the branch certificate. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    let finite := contract.finiteContract previous active
    let execution :=
      finite.firstHit (contract.event previous active)
        (contract.eventDecidable previous active)
    match found : execution.hit? with
    | some hit =>
        Certificate.hit
          ⟨hit.value, hit.member, hit.sound⟩
    | none =>
        Certificate.noEvent (by
          intro existsHit
          rcases existsHit with ⟨item, member, holds⟩
          rcases (finite.schedule.mem_iff_exists_index item).mp member with
            ⟨index, rfl⟩
          exact (execution.exhaustive found index) holds)

/-- Uncounted public executor. -/
def execute (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

/-- Public CT-style executor spelling. -/
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

/-- Read the latest schedule-event certificate. -/
def latestCertificate :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.Certificate stage.previous
        (show focus.Active stage.previous from active) :=
  Focus.ActiveQuery.latest

/-- Focus on the first-hit branch. -/
def hitRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ hit : contract.ExistsEvent stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.hit hit)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | hit hit => exact isTrue ⟨hit, rfl⟩
      | noEvent _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨hit, equal⟩
            cases equal)))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

/-- Focus on the no-event branch. -/
def noEventRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ noEvent : contract.NoEvent stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.noEvent noEvent)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | hit _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨noEvent, equal⟩
            cases equal)
      | noEvent noEvent => exact isTrue ⟨noEvent, rfl⟩))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

/-- Live focus containing exactly the event-hit branch. -/
abbrev hitFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.hitRefinement

/-- Live focus containing exactly the no-event branch. -/
abbrev noEventFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.noEventRefinement

/-- Read the event witness on the hit branch. -/
def hitQuery :
    Focus.ActiveQuery contract.hitFocus fun stage active =>
      contract.ExistsEvent stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

/-- Read the no-event residual on the complementary branch. -/
def noEventQuery :
    Focus.ActiveQuery contract.noEventFocus fun stage active =>
      contract.NoEvent stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

/-- Convert the no-event residual into pointwise absence over the exact
residual-owned schedule. -/
def pointwiseAbsentQuery :
    Focus.ActiveQuery contract.noEventFocus fun stage active =>
      ∀ item ∈ ((contract.schedule.preserve).read stage active.parent).values,
        Not (contract.event stage.previous active.parent item
          ((contract.runner.preserve).read stage active.parent item)) :=
  contract.noEventQuery.map fun stage active noEvent =>
    (contract.finiteContract stage.previous active.parent)
      |>.pointwise_absent_of_noEvent
        (contract.event stage.previous active.parent) noEvent

/-- On the no-event branch, read each scheduled runner output together with
the proof that the excluded event is absent for that exact output.  This is the
Core-owned residual payload used by graph and PDE specializations to carry
silent/germ packets downstream without a custom handoff. -/
def pointwiseAbsentOutputQuery :
    Focus.ActiveQuery contract.noEventFocus fun stage active =>
      ∀ item,
        item ∈ ((contract.schedule.preserve).read stage active.parent).values ->
          { output :
              contract.Output stage.previous active.parent item //
              Not (contract.event stage.previous active.parent item output) } :=
  Focus.ActiveQuery.ofFunction fun stage active item member =>
    ⟨(contract.runner.preserve).read stage active.parent item,
      contract.pointwiseAbsentQuery.read stage active item member⟩

/-- Refine a no-event branch to any residual predicate that follows from
absence of the excluded event for each exact runner output. -/
def pointwiseRemainingQuery
    (Remaining : (previous : Previous) -> (active : focus.Active previous) ->
      (item : contract.Item) -> contract.Output previous active item -> Prop)
    (remaining_of_absent :
      ∀ previous active item
        (output : contract.Output previous active item),
          Not (contract.event previous active item output) ->
            Remaining previous active item output) :
    Focus.ActiveQuery contract.noEventFocus fun stage active =>
      ∀ item,
        item ∈ ((contract.schedule.preserve).read stage active.parent).values ->
          Remaining stage.previous active.parent item
            ((contract.runner.preserve).read stage active.parent item) :=
  Focus.ActiveQuery.ofFunction fun stage active item member =>
    remaining_of_absent stage.previous active.parent item
      ((contract.pointwiseAbsentOutputQuery.read stage active item member).1)
      ((contract.pointwiseAbsentOutputQuery.read stage active item member).2)

end FocusedContract

end Hypostructure.Core.Finite.ScheduleEvents
