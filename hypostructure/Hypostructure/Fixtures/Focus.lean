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

def firstCounted (decision : Decision.Stage (fun value : Bool => value = true)
    (fun value => Not (value = true))) :
    Core.Counted (Focus.Stage branchFocus firstOutput) :=
  Focus.runCounted branchFocus decision fun _active _checks _exact => 2

def first (decision : Decision.Stage (fun value : Bool => value = true)
    (fun value => Not (value = true))) :
    Focus.Stage branchFocus firstOutput :=
  (firstCounted decision).value

/-- A nonzero local payload schedule used to test sequential work
composition with the branch selector. -/
def payloadBudget : Core.PolynomialCheckBudget
    (Decision.Stage (fun value : Bool => value = true)
      (fun value => Not (value = true))) :=
  Core.PolynomialCheckBudget.constant (fun _decision => 0) 4

abbrev payloadOutput (stage : Decision.Stage
    (fun value : Bool => value = true)
    (fun value => Not (value = true)))
    (_active : branchFocus.Active stage) :=
  Nat

def activePayload (stage : Decision.Stage
    (fun value : Bool => value = true)
    (fun value => Not (value = true)))
    (active : branchFocus.Active stage)
    (_selectionChecks : Nat)
    (_exact : _selectionChecks = branchFocus.selectionBudget.checks stage) :
    Core.Counted (payloadOutput stage active) :=
  ⟨7, 4⟩

theorem activePayload_checks (stage : Decision.Stage
    (fun value : Bool => value = true)
    (fun value => Not (value = true)))
    (active : branchFocus.Active stage)
    (selectionChecks : Nat)
    (exact : selectionChecks = branchFocus.selectionBudget.checks stage) :
    (activePayload stage active selectionChecks exact).checks =
      payloadBudget.checks stage :=
  rfl

def payloadCounted (decision : Decision.Stage
    (fun value : Bool => value = true)
    (fun value => Not (value = true))) :
    Core.Counted (Focus.Stage branchFocus payloadOutput) :=
  Focus.runCountedPayload branchFocus payloadBudget decision
    (activePayload decision) (activePayload_checks decision)

def yesPayload := (payloadCounted yesDecision).value

def noPayload := (payloadCounted noDecision).value

abbrev payloadFocus := Focus.successor branchFocus payloadOutput

def payloadQuery : Focus.ActiveQuery payloadFocus fun stage proof =>
    payloadOutput stage.previous proof :=
  Focus.ActiveQuery.latest

abbrev firstFocus := Focus.successor branchFocus firstOutput

def firstQuery : Focus.ActiveQuery firstFocus fun stage proof =>
    firstOutput stage.previous proof :=
  Focus.ActiveQuery.latest

abbrev secondOutput (stage : Focus.Stage branchFocus firstOutput)
    (active : firstFocus.Active stage) :=
  { value : Nat // value = firstQuery.read stage active + 1 }

def secondCounted (stage : Focus.Stage branchFocus firstOutput) :
    Core.Counted (Focus.Stage firstFocus secondOutput) :=
  Focus.runCounted firstFocus stage fun active _checks _exact =>
    ⟨firstQuery.read stage active + 1, rfl⟩

def second (stage : Focus.Stage branchFocus firstOutput) :
    Focus.Stage firstFocus secondOutput :=
  (secondCounted stage).value

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

def yesView : Focus.ActiveView branchFocus :=
  Focus.ActiveView.of yesDecision yesActive

def focusedBoolean : Focus.ActiveQuery branchFocus fun _stage _active => Bool :=
  Focus.yesProof.map fun stage _active _proof => stage.previous

def focusedBooleanOnView : Query (Focus.ActiveView branchFocus)
    (fun _view => Bool) :=
  focusedBoolean.onView

theorem active_view_reads_exact_predecessor :
    focusedBooleanOnView.read yesView = true :=
  rfl

theorem active_view_is_only_a_query_root :
    residualOf yesView = yesView :=
  rfl

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

theorem branch_focus_checks_yes :
    (firstCounted yesDecision).checks = 1 :=
  rfl

theorem branch_focus_checks_no :
    (firstCounted noDecision).checks = 1 :=
  rfl

theorem active_payload_value :
    payloadQuery.read yesPayload yesActive = 7 :=
  rfl

theorem active_payload_exact_total :
    (payloadCounted yesDecision).checks = 5 :=
  rfl

theorem inactive_payload_selector_only :
    (payloadCounted noDecision).checks = 1 :=
  rfl

theorem active_payload_composed_equation :
    (payloadCounted yesDecision).checks =
      (branchFocus.selectionBudget.add payloadBudget).checks yesDecision :=
  Focus.runCountedPayload_checks_of_active branchFocus payloadBudget yesDecision
    (activePayload yesDecision) (activePayload_checks yesDecision) yesActive

theorem inactive_payload_exact_equation :
    (payloadCounted noDecision).checks =
      branchFocus.selectionBudget.checks noDecision :=
  Focus.runCountedPayload_checks_of_inactive branchFocus payloadBudget noDecision
    (activePayload noDecision) (activePayload_checks noDecision) noInactive

theorem payload_retains_predecessor :
    (payloadCounted yesDecision).value.previous = yesDecision :=
  Focus.runCountedPayload_previous branchFocus payloadBudget yesDecision
    (activePayload yesDecision) (activePayload_checks yesDecision)

theorem active_payload_work_bounded :
    (payloadCounted yesDecision).checks <=
      (branchFocus.selectionBudget.add payloadBudget).coefficient *
        ((branchFocus.selectionBudget.add payloadBudget).size yesDecision + 1) ^
          (branchFocus.selectionBudget.add payloadBudget).degree :=
  Focus.runCountedPayload_checks_bounded branchFocus payloadBudget yesDecision
    (activePayload yesDecision) (activePayload_checks yesDecision)

theorem inactive_payload_work_bounded :
    (payloadCounted noDecision).checks <=
      (branchFocus.selectionBudget.add payloadBudget).coefficient *
        ((branchFocus.selectionBudget.add payloadBudget).size noDecision + 1) ^
          (branchFocus.selectionBudget.add payloadBudget).degree :=
  Focus.runCountedPayload_checks_bounded branchFocus payloadBudget noDecision
    (activePayload noDecision) (activePayload_checks noDecision)

theorem successor_focus_preserves_selection_checks :
    (secondCounted yesFirst).checks =
      (firstCounted yesFirst.previous).checks :=
  rfl

theorem branch_focus_work_bounded :
    (firstCounted yesDecision).checks <=
      branchFocus.selectionBudget.coefficient *
        (branchFocus.selectionBudget.size yesDecision + 1) ^
          branchFocus.selectionBudget.degree :=
  Focus.runCounted_checks_bounded branchFocus yesDecision _

/-! ## Counted refinement -/

/-- Core compares the inherited Boolean tag; the fixture supplies no raw
selector or work budget. -/
def acceptRefinement : Focus.Refinement branchFocus :=
  focusedBoolean.equalTo true

/-- The same parent can remain active while the child equality rejects. -/
def rejectRefinement : Focus.Refinement branchFocus :=
  focusedBoolean.equalTo false

abbrev refinedFocus := Focus.refine branchFocus acceptRefinement
abbrev rejectedFocus := Focus.refine branchFocus rejectRefinement

def refinedYesActive : refinedFocus.Active yesDecision :=
  match _selected : (refinedFocus.select yesDecision).value with
  | .isTrue proof => proof
  | .isFalse absent =>
      False.elim (absent {
        parent := yesActive
        accepted := rfl
      })

def refinedNoInactive : Not (refinedFocus.Active noDecision) :=
  fun active => noInactive active.parent

def rejectedYesInactive : Not (rejectedFocus.Active yesDecision) := by
  intro active
  have parentEq : active.parent = yesActive := Subsingleton.elim _ _
  cases parentEq
  have accepted := active.accepted
  simp [rejectRefinement, Focus.ActiveQuery.equalTo,
    Focus.ActiveQuery.tagEqualTo, focusedBoolean, yesDecision, positive,
    Decision.Node.run, Decision.Node.complement, Decision.Node.create,
    isTrueDecidable] at accepted

def refinedBoolean : Focus.ActiveQuery refinedFocus fun _stage _active => Bool :=
  focusedBoolean.narrow acceptRefinement

abbrev refinedOutput (_stage : Decision.Stage
    (fun value : Bool => value = true)
    (fun value => Not (value = true)))
    (_active : refinedFocus.Active _stage) := Nat

def refinedCounted :=
  Focus.runCounted refinedFocus yesDecision
    (Output := refinedOutput) fun _active _checks _exact => 11

def rejectedCounted :=
  Focus.runCounted rejectedFocus yesDecision
    (Output := fun _stage _active => Nat)
    fun active _checks _exact => False.elim (rejectedYesInactive active)

theorem refined_selector_accepts_actual_branch :
    match (refinedFocus.select yesDecision).value with
    | .isTrue _proof => True
    | .isFalse _absent => False := by
  change True
  trivial

theorem rejected_selector_rejects_actual_child :
    match (rejectedFocus.select yesDecision).value with
    | .isTrue _proof => False
    | .isFalse _absent => True := by
  change True
  trivial

theorem refined_selector_rejects_inactive_parent :
    match (refinedFocus.select noDecision).value with
    | .isTrue _proof => False
    | .isFalse _absent => True := by
  change True
  trivial

theorem refined_active_pays_parent_and_child :
    (refinedFocus.select yesDecision).checks = 2 := by
  change (Focus.selectRefined branchFocus acceptRefinement
    yesDecision).checks = 2
  calc
    _ = branchFocus.selectionBudget.checks yesDecision +
        acceptRefinement.decisionBudget.checks yesDecision :=
      Focus.selectRefined_checks_of_parent_active branchFocus
        acceptRefinement yesDecision yesActive
    _ = 2 := rfl

theorem rejected_child_pays_parent_and_child :
    (rejectedFocus.select yesDecision).checks = 2 := by
  change (Focus.selectRefined branchFocus rejectRefinement
    yesDecision).checks = 2
  calc
    _ = branchFocus.selectionBudget.checks yesDecision +
        rejectRefinement.decisionBudget.checks yesDecision :=
      Focus.selectRefined_checks_of_parent_active branchFocus
        rejectRefinement yesDecision yesActive
    _ = 2 := rfl

theorem refined_inactive_parent_skips_child :
    (refinedFocus.select noDecision).checks = 1 := by
  change (Focus.selectRefined branchFocus acceptRefinement
    noDecision).checks = 1
  calc
    _ = branchFocus.selectionBudget.checks noDecision :=
      Focus.selectRefined_checks_of_parent_inactive branchFocus
        acceptRefinement noDecision noInactive
    _ = 1 := rfl

theorem refined_dynamic_budget_is_exact (decision) :
    (refinedFocus.select decision).checks =
      refinedFocus.selectionBudget.checks decision :=
  refinedFocus.select_checks decision

theorem refined_query_reads_parent_ledger :
    refinedBoolean.read yesDecision refinedYesActive = true :=
  rfl

theorem refined_query_exposes_selected_child_proof :
    focusedBoolean.read yesDecision refinedYesActive.parent = true :=
  (focusedBoolean.equalToProof true).read yesDecision refinedYesActive

theorem refined_execution_retains_literal_predecessor :
    refinedCounted.value.previous = yesDecision := by
  exact Focus.runCounted_previous refinedFocus yesDecision _

theorem refined_execution_uses_exact_selector_work :
    refinedCounted.checks = 2 := by
  change (refinedFocus.select yesDecision).checks = 2
  exact refined_active_pays_parent_and_child

theorem rejected_execution_uses_exact_selector_work :
    rejectedCounted.checks = 2 := by
  change (rejectedFocus.select yesDecision).checks = 2
  exact rejected_child_pays_parent_and_child

theorem rejected_child_emits_inactive :
    Exists fun absent => rejectedCounted.value.added =
      Focus.Outcome.inactive absent := by
  cases branch : rejectedCounted.value.added with
  | active proof _output => exact (rejectedYesInactive proof).elim
  | inactive absent => exact ⟨absent, branch⟩

#print axioms yes_second_value
#print axioms no_second_inactive
#print axioms branch_focus_checks_yes
#print axioms branch_focus_checks_no
#print axioms active_payload_value
#print axioms active_payload_exact_total
#print axioms inactive_payload_selector_only
#print axioms active_payload_composed_equation
#print axioms inactive_payload_exact_equation
#print axioms active_view_reads_exact_predecessor
#print axioms active_view_is_only_a_query_root
#print axioms payload_retains_predecessor
#print axioms active_payload_work_bounded
#print axioms inactive_payload_work_bounded
#print axioms successor_focus_preserves_selection_checks
#print axioms branch_focus_work_bounded
#print axioms refined_active_pays_parent_and_child
#print axioms rejected_child_pays_parent_and_child
#print axioms refined_inactive_parent_skips_child
#print axioms refined_dynamic_budget_is_exact
#print axioms refined_query_reads_parent_ledger
#print axioms refined_query_exposes_selected_child_proof
#print axioms refined_execution_retains_literal_predecessor
#print axioms refined_execution_uses_exact_selector_work
#print axioms rejected_execution_uses_exact_selector_work
#print axioms rejected_child_emits_inactive

end Hypostructure.Fixtures.Focus
