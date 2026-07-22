import Hypostructure.CT3.Execution
import Hypostructure.Core.Finite.Search
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Focus

/-!
# CT3 schedule classification

This module owns the schedule-wide CT3 terminal split.  A domain contract
supplies an exact residual-owned item schedule and the CT3 terminal produced
for each item.  CT3 derives the all-good branch, the first residual branch,
and terminal-family membership without problem-specific routing.
-/

namespace Hypostructure.CT3.Schedule

open Hypostructure.Core
open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

universe uPrevious u

/-- Minimal public contract for a finite schedule of CT3 item executions. -/
structure Contract (Item : Type u) where
  items : Enumeration Item
  terminal : Item -> Terminal

namespace Contract

variable {Item : Type u} (contract : Contract Item)

def GoodTerminal (item : Item) : Prop :=
  contract.terminal item = .compression ∨ contract.terminal item = .knownRow

def ResidualTerminal (item : Item) : Prop :=
  contract.terminal item = .distinguishing ∨ contract.terminal item = .novelRow

def AllGood : Prop :=
  ∀ item ∈ contract.items.values, contract.GoodTerminal item

def HasResidual : Prop :=
  ∃ item ∈ contract.items.values, contract.ResidualTerminal item

def residualDecidable (item : Item) :
    Decidable (contract.ResidualTerminal item) := by
  unfold ResidualTerminal
  infer_instance

def residualSearch :
    Search.Execution contract.items contract.ResidualTerminal :=
  Search.run contract.items contract.ResidualTerminal contract.residualDecidable

theorem good_or_residual (item : Item) :
    contract.GoodTerminal item ∨ contract.ResidualTerminal item := by
  cases terminal_eq : contract.terminal item <;>
    simp [GoodTerminal, ResidualTerminal, terminal_eq]

theorem allGood_or_hasResidual :
    contract.AllGood ∨ contract.HasResidual := by
  classical
  by_cases allGood : contract.AllGood
  · exact Or.inl allGood
  · refine Or.inr ?_
    by_contra noResidual
    apply allGood
    intro item member
    cases contract.good_or_residual item with
    | inl good => exact good
    | inr residual =>
        exact (noResidual ⟨item, member, residual⟩).elim

theorem hasResidual_of_not_allGood (notAllGood : Not contract.AllGood) :
    contract.HasResidual := by
  cases contract.allGood_or_hasResidual with
  | inl allGood => exact (notAllGood allGood).elim
  | inr residual => exact residual

theorem firstResidual_of_hasResidual (hasResidual : contract.HasResidual) :
    ∃ hit : Search.IndexedHit contract.items contract.ResidualTerminal,
      (contract.residualSearch).hit? = some hit := by
  cases found : contract.residualSearch.hit? with
  | some hit => exact ⟨hit, rfl⟩
  | none =>
      rcases hasResidual with ⟨item, member, residual⟩
      rcases (contract.items.mem_iff_exists_index item).mp member with
        ⟨index, rfl⟩
      have avoids := contract.residualSearch.exhaustive found
      exact (avoids index residual).elim

/-- Good terminals are exactly the witness-bearing CT3 terminals used by the
compression-style branch. -/
theorem good_terminal_cases {item : Item}
    (good : contract.GoodTerminal item) :
    contract.terminal item = .compression ∨
      contract.terminal item = .knownRow :=
  good

/-- Residual terminals are exactly the CT3 residual branches. -/
theorem residual_terminal_cases {item : Item}
    (residual : contract.ResidualTerminal item) :
    contract.terminal item = .distinguishing ∨
      contract.terminal item = .novelRow :=
  residual

end Contract

/-! ## Focused residual executor -/

/-- Residual-owned CT3 terminal schedule contract.  The active predecessor
owns the exact item schedule and item terminal map; CT3 owns the all-good vs
first-residual split and installs the selected branch in the ledger. -/
structure FocusedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type u
  items : Focus.ActiveQuery focus fun _previous _active => Enumeration Item
  terminal : (previous : Previous) -> focus.Active previous -> Item -> Terminal

namespace FocusedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedContract focus)

/-- Pure schedule contract seen at one active predecessor. -/
def scheduleAt (previous : Previous) (active : focus.Active previous) :
    Contract contract.Item where
  items := contract.items.read previous active
  terminal := contract.terminal previous active

def AllGood (previous : Previous) (active : focus.Active previous) : Prop :=
  (contract.scheduleAt previous active).AllGood

def HasResidual (previous : Previous) (active : focus.Active previous) : Prop :=
  (contract.scheduleAt previous active).HasResidual

def FirstResidual (previous : Previous) (active : focus.Active previous) : Type :=
  Search.IndexedHit (contract.items.read previous active)
    (contract.scheduleAt previous active).ResidualTerminal

def FirstResidual.hasResidual {previous : Previous}
    {active : focus.Active previous}
    (hit : contract.FirstResidual previous active) :
    contract.HasResidual previous active :=
  ⟨hit.value, hit.member, hit.sound⟩

inductive Certificate (previous : Previous)
    (active : focus.Active previous) : Type where
  | allGood : contract.AllGood previous active ->
      Certificate previous active
  | hasResidual : contract.FirstResidual previous active ->
      Certificate previous active

abbrev Stage :=
  Focus.Stage focus fun previous active =>
    contract.Certificate previous active

/-- Execute the CT3 terminal-family split and register the selected branch. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    let schedule := contract.scheduleAt previous active
    let search := schedule.residualSearch
    match found : search.hit? with
    | some hit =>
        Certificate.hasResidual hit
    | none =>
        Certificate.allGood (by
          intro item member
          cases schedule.good_or_residual item with
          | inl good => exact good
          | inr residual =>
              rcases (schedule.items.mem_iff_exists_index item).mp member with
                ⟨index, rfl⟩
              exact (search.exhaustive found index residual).elim)

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
      contract.Certificate stage.previous
        (show focus.Active stage.previous from active) :=
  Focus.ActiveQuery.latest

def allGoodRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ allGood : contract.AllGood stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.allGood allGood)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | allGood allGood => exact isTrue ⟨allGood, rfl⟩
      | hasResidual _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨allGood, equal⟩
            cases equal)))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

def residualRefinement : Focus.Refinement contract.successor :=
  Focus.Refinement.ofDecision
    (fun stage active =>
      ∃ firstResidual : contract.FirstResidual stage.previous active,
        contract.latestCertificate.read stage active =
          Certificate.hasResidual firstResidual)
    (fun stage active => Counted.pure (by
      cases certificate : contract.latestCertificate.read stage active with
      | allGood _ =>
          exact isFalse (by
            intro witness
            rcases witness with ⟨firstResidual, equal⟩
            cases equal)
      | hasResidual firstResidual => exact isTrue ⟨firstResidual, rfl⟩))
    (PolynomialCheckBudget.proofOnly contract.Stage)
    (fun _stage _active => rfl)

abbrev allGoodFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.allGoodRefinement

abbrev residualFocus : Focus.Profile contract.Stage :=
  Focus.refine contract.successor contract.residualRefinement

def allGoodQuery :
    Focus.ActiveQuery contract.allGoodFocus fun stage active =>
      contract.AllGood stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

noncomputable def residualQuery :
    Focus.ActiveQuery contract.residualFocus fun stage active =>
      contract.FirstResidual stage.previous active.parent :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    Classical.choose active.accepted

noncomputable def hasResidualQuery :
    Focus.ActiveQuery contract.residualFocus fun stage active =>
      contract.HasResidual stage.previous active.parent :=
  contract.residualQuery.map fun _stage _active hit =>
    hit.hasResidual

noncomputable def residualItemQuery :
    Focus.ActiveQuery contract.residualFocus fun _stage _active =>
      contract.Item :=
  contract.residualQuery.map fun _stage _active hit =>
    hit.value

noncomputable def residualTerminalQuery :
    Focus.ActiveQuery contract.residualFocus fun stage active =>
      (contract.scheduleAt stage.previous active.parent).ResidualTerminal
        (contract.residualItemQuery.read stage active) :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    (contract.residualQuery.read stage active).sound

end FocusedContract

end Hypostructure.CT3.Schedule
