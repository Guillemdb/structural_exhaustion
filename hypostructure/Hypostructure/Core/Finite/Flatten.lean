import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Focus

/-!
# Exact dependent schedule flattening

`DependentEnumeration.flatten` already owns the flattened order.  This module
adds reusable count certificates for the common proof pattern where every
fibre has a fixed contribution.
-/

namespace Hypostructure.Core.Finite.Flatten

open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

universe uPrevious u v

private theorem sum_map_constant {index : Type u} {fibre : index -> Type v}
    (fibres : (i : index) -> Enumeration (fibre i))
    (values : List index) (contribution : Nat)
    (all_fibres : ∀ index ∈ values,
      (fibres index).card = contribution) :
    (values.map fun i => (fibres i).card).sum =
      contribution * values.length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have head_eq : (fibres head).card = contribution :=
        all_fibres head (by simp)
      have tail_all : ∀ index ∈ tail,
          (fibres index).card = contribution := by
        intro index member
        exact all_fibres index (by simp [member])
      simp only [List.map_cons, List.sum_cons, List.length_cons, head_eq,
        ih tail_all]
      rw [Nat.mul_succ]
      exact Nat.add_comm _ _

/-- A flattened dependent schedule together with its framework-derived exact
cardinality formula. -/
structure Result {index : Type u} {fibre : index -> Type v}
    (schedule : DependentEnumeration index fibre) where
  flattened : Enumeration (Sigma fibre)
  flattened_eq : flattened = schedule.flatten
  card_eq_sum :
    flattened.card =
      (schedule.indices.values.map fun i => (schedule.fibres i).card).sum

/-- Execute dependent flattening in index-major order. -/
def run {index : Type u} {fibre : index -> Type v}
    (schedule : DependentEnumeration index fibre) :
    Result schedule where
  flattened := schedule.flatten
  flattened_eq := rfl
  card_eq_sum := DependentEnumeration.card_flatten schedule

namespace Result

/-- If every fibre has size `contribution`, the flattened cardinality is the
contribution times the number of indices. -/
theorem card_eq_contribution_mul {index : Type u} {fibre : index -> Type v}
    {schedule : DependentEnumeration index fibre}
    (result : Result schedule) (contribution : Nat)
    (all_fibres : ∀ index ∈ schedule.indices.values,
      (schedule.fibres index).card = contribution) :
    result.flattened.card = contribution * schedule.indices.card := by
  rw [result.card_eq_sum]
  exact sum_map_constant schedule.fibres schedule.indices.values contribution
    all_fibres

end Result

/-! ## Focused residual executor -/

/-- Residual-owned dependent-flatten contract.  The active predecessor owns
the exact dependent schedule; Core owns flattening order, the ledger
extension, and the cardinality identities. -/
structure FocusedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Index : Type u
  Fibre : Index -> Type v
  schedule : Focus.ActiveQuery focus fun _previous _active =>
    DependentEnumeration Index Fibre

namespace FocusedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedContract focus)

/-- Pure flattening result seen at one active predecessor. -/
def resultAt (previous : Previous) (active : focus.Active previous) :
    Result (contract.schedule.read previous active) :=
  run (contract.schedule.read previous active)

/-- Focused stage carrying exactly one Core-owned flattening result. -/
abbrev Stage :=
  Focus.Stage focus fun previous active =>
    Result (contract.schedule.read previous active)

/-- Execute dependent flattening and register the flattened exact schedule. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    contract.resultAt previous active

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
    Result (contract.schedule.read previous active)

/-- Read the complete flattening result from the newest ledger extension. -/
def latestResult :
    Focus.ActiveQuery contract.successor fun stage active =>
      Result (contract.schedule.read stage.previous active) :=
  Focus.ActiveQuery.latest

/-- Read the flattened exact schedule from the newest ledger extension. -/
def latestFlattened :
    Focus.ActiveQuery contract.successor fun _stage _active =>
      Enumeration (Sigma contract.Fibre) :=
  contract.latestResult.map fun _stage _active result =>
    result.flattened

/-- Read the exact sum-cardinality formula from the newest ledger extension. -/
def latestCardEqSum :
    Focus.ActiveQuery contract.successor fun stage active =>
      (contract.latestFlattened.read stage active).card =
        (((contract.schedule.preserve).read stage active).indices.values.map
          fun i => (((contract.schedule.preserve).read stage active).fibres i).card).sum :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    (contract.latestResult.read stage active).card_eq_sum

/-- If every active fibre has the same size, read the constant-contribution
cardinality formula for the latest flattened schedule. -/
def latestCardEqContributionMul
    (contribution : Nat)
    (all_fibres : Focus.ActiveQuery contract.successor fun stage active =>
      ∀ index ∈ ((contract.schedule.preserve).read stage active).indices.values,
        (((contract.schedule.preserve).read stage active).fibres index).card =
          contribution) :
    Focus.ActiveQuery contract.successor fun stage active =>
      (contract.latestFlattened.read stage active).card =
        contribution *
          ((contract.schedule.preserve).read stage active).indices.card :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    (contract.latestResult.read stage active).card_eq_contribution_mul
      contribution (all_fibres.read stage active)

end FocusedContract

end Hypostructure.Core.Finite.Flatten
