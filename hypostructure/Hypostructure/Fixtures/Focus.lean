import Hypostructure.Core.Residual.Focus

/-!
# Repeatable branch-focus fixture

The fixture advances the yes arm twice, reads the first payload through an
active query, and verifies that the no sibling receives no fabricated data.
-/

namespace Hypostructure.Fixtures.Focus

open Hypostructure.Core.Residual

def isTrueDecidable : (value : Bool) -> Decidable (value = true)
  | true => .isTrue rfl
  | false => .isFalse (by simp)

def positive : Decision.Node Bool (fun value => value = true)
    (fun value => Not (value = true)) :=
  Decision.Node.complement _ isTrueDecidable

def yesDecision := positive.run true

def noDecision := positive.run false

abbrev branchFocus :=
  Focus.yes (Yes := fun value : Bool => value = true)
    (No := fun value => Not (value = true))

abbrev firstOutput (stage : Decision.Stage (fun value : Bool => value = true)
    (fun value => Not (value = true))) (_active : branchFocus.Active stage) :=
  Nat

def first (decision : Decision.Stage (fun value : Bool => value = true)
    (fun value => Not (value = true))) :
  Focus.Stage branchFocus firstOutput :=
  Focus.run branchFocus decision fun _active => 2

abbrev firstFocus := Focus.successor branchFocus firstOutput

def firstQuery : Focus.ActiveQuery firstFocus fun stage proof =>
    firstOutput stage.previous proof :=
  Focus.ActiveQuery.latest

abbrev secondOutput (stage : Focus.Stage branchFocus firstOutput)
    (active : firstFocus.Active stage) :=
  { value : Nat // value = firstQuery.read stage active + 1 }

def second (stage : Focus.Stage branchFocus firstOutput) :
    Focus.Stage firstFocus secondOutput :=
  Focus.run firstFocus stage fun active =>
    ⟨firstQuery.read stage active + 1, rfl⟩

def yesFirst := first yesDecision

def yesSecond := second yesFirst

def noFirst := first noDecision

def noSecond := second noFirst

def yesActive : branchFocus.Active yesDecision where
  proof := rfl
  selected := rfl

def noInactive : Not (branchFocus.Active noDecision) := by
  intro active
  have selected := active.selected
  simp [noDecision, positive, Decision.Node.run, Decision.Node.complement,
    Decision.Node.create, isTrueDecidable] at selected

def noFirstInactive : Not (firstFocus.Active noFirst) :=
  noInactive

theorem yes_first_value : firstQuery.read yesFirst yesActive = 2 :=
  rfl

theorem yes_second_value :
    (Focus.ActiveQuery.latest.read yesSecond yesActive).1 = 3 :=
  rfl

theorem second_retains_first : yesSecond.previous = yesFirst :=
  rfl

theorem no_first_inactive :
    ∃ absent, noFirst.added =
      Focus.Outcome.inactive absent := by
  cases branch : noFirst.added with
  | active proof _output => exact (noInactive proof).elim
  | inactive absent => exact ⟨absent, branch⟩

theorem no_second_inactive :
    ∃ absent, noSecond.added =
      Focus.Outcome.inactive absent := by
  cases branch : noSecond.added with
  | active proof _output => exact (noFirstInactive proof).elim
  | inactive absent => exact ⟨absent, branch⟩

#print axioms yes_second_value
#print axioms no_second_inactive

end Hypostructure.Fixtures.Focus
