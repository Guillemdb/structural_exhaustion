import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Focus

/-!
# Residual-owned selected schedules

This module packages the common pattern where a branch exposes an exact finite
subschedule already readable from the predecessor ledger.  Core installs the
selected schedule as a proof-only focused extension and provides successor
queries; applications do not rebuild lists downstream.
-/

namespace Hypostructure.Core.Finite.SelectedSchedule

open Hypostructure.Core
open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

universe uPrevious uItem

/-- Public contract for a selected exact schedule on an active residual. -/
structure Contract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type uItem
  selected : Focus.ActiveQuery focus fun _previous _active => Enumeration Item

namespace Contract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : Contract focus)

/-- One framework-owned selected schedule certificate. -/
structure Certificate (previous : Previous) (active : focus.Active previous) where
  schedule : Enumeration contract.Item
  exact : schedule = contract.selected.read previous active

/-- Focused stage carrying only the selected schedule certificate. -/
abbrev Stage :=
  Focus.Stage focus fun previous active => contract.Certificate previous active

/-- Execute the selected-schedule projection.  No local computation is
charged beyond the inherited focus selection. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    { schedule := contract.selected.read previous active
      exact := rfl }

def execute (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

/-- Public executor spelling used by CT-facing code. -/
abbrev run (previous : Previous) : contract.Stage :=
  contract.execute previous

@[simp] theorem execute_previous (previous : Previous) :
    (contract.execute previous).previous = previous :=
  Focus.runCounted_previous focus previous _

@[simp] theorem run_previous (previous : Previous) :
    (contract.run previous).previous = previous :=
  contract.execute_previous previous

theorem executeCounted_checks (previous : Previous) :
    (contract.executeCounted previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor focus fun previous active =>
    contract.Certificate previous active

/-- Read the exact selected schedule from the newest framework extension. -/
def latestSchedule :
    Focus.ActiveQuery contract.successor fun _stage _active =>
      Enumeration contract.Item :=
  (Focus.ActiveQuery.latest).map fun _stage _active certificate =>
    certificate.schedule

/-- Read exact evidence that the latest schedule is the predecessor-owned
selected schedule. -/
def latestScheduleExact :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.latestSchedule.read stage active =
        contract.selected.read stage.previous active :=
  Focus.ActiveQuery.ofFunction fun _stage active =>
    (Focus.ActiveQuery.latest.read _stage active).exact

/-- Read the selected schedule cardinality from the newest framework
extension.  Downstream nodes should use this query rather than rebuild or
copy a count into an application-owned output. -/
def latestCard :
    Focus.ActiveQuery contract.successor fun _stage _active => Nat :=
  contract.latestSchedule.map fun _stage _active schedule =>
    schedule.card

/-- Read exact evidence that the latest cardinality is the predecessor-owned
selected schedule cardinality. -/
def latestCardExact :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.latestCard.read stage active =
        (contract.selected.read stage.previous active).card :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    exact congrArg Enumeration.card
      (Focus.ActiveQuery.latest.read stage active).exact

/-- Transfer membership in the latest selected schedule back to the exact
predecessor-owned selected schedule. -/
def latestMemberExact :
    Focus.ActiveQuery contract.successor fun stage active =>
      ∀ item,
        item ∈ (contract.latestSchedule.read stage active).values ->
          item ∈ (contract.selected.read stage.previous active).values :=
  Focus.ActiveQuery.ofFunction fun stage active item member => by
    rw [contract.latestScheduleExact.read stage active] at member
    exact member

/-- Read the selected entries as a schedule of membership-carrying values.
This is the Core-owned item-level residual for downstream graph/PDE schedule
construction. -/
def latestAttached :
    Focus.ActiveQuery contract.successor fun stage active =>
      Enumeration
        { item : contract.Item //
          item ∈ (contract.selected.read stage.previous active).values } :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    (contract.latestSchedule.read stage active).attach.map
      (fun item =>
        ⟨item.1, contract.latestMemberExact.read stage active item.1 item.2⟩)
      (by
        intro left right equal
        have value_eq : left.1 = right.1 :=
          congrArg
            (fun output :
              { item : contract.Item //
                item ∈ (contract.selected.read stage.previous active).values } =>
              output.1)
            equal
        exact Subtype.ext value_eq)
      (by
        letI : DecidableEq contract.Item :=
          (contract.selected.read stage.previous active).decEq
        exact inferInstance)

/-- The attached selected-entry schedule has exactly the selected schedule
cardinality. -/
def latestAttachedCardExact :
    Focus.ActiveQuery contract.successor fun stage active =>
      (contract.latestAttached.read stage active).card =
        (contract.selected.read stage.previous active).card :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    simpa [latestAttached, Enumeration.map, Enumeration.attach,
      Enumeration.card] using
      congrArg Enumeration.card
        (contract.latestScheduleExact.read stage active)

@[simp] theorem latestSchedule_read_active (previous : Previous)
    (active : focus.Active previous) :
    contract.latestSchedule.read
        (Ledger.extend previous
          (.active active
            ({ schedule := contract.selected.read previous active
               exact := rfl } :
              contract.Certificate previous active)))
        active =
      contract.selected.read previous active :=
  rfl

@[simp] theorem latestCard_read_active (previous : Previous)
    (active : focus.Active previous) :
    contract.latestCard.read
        (Ledger.extend previous
          (.active active
            ({ schedule := contract.selected.read previous active
               exact := rfl } :
              contract.Certificate previous active)))
        active =
      (contract.selected.read previous active).card :=
  rfl

end Contract

end Hypostructure.Core.Finite.SelectedSchedule
