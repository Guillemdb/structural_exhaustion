import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.Search

/-!
# Finite scan accounting

This module records exact finite counts and the visible primitive inspections
performed by the canonical first-hit runner.  The mathematical resource budget
API is intentionally not used here: these are verifier-work counts.
-/

namespace Hypostructure.Core.Finite.Accounting

open Hypostructure.Core
open Hypostructure.Core.Finite

universe u v

/-- Exact number of scheduled members satisfying a decidable predicate. -/
def countWhere {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) : Nat :=
  schedule.values.countP fun value =>
    @decide (predicate value) (decidePredicate value)

theorem countWhere_le_card {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    countWhere schedule predicate decidePredicate <= schedule.card := by
  exact List.countP_le_length

/-- The exact count agrees with filtering the same ordered schedule. -/
theorem countWhere_eq_filter_length {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    countWhere schedule predicate decidePredicate =
      (schedule.values.filter fun value =>
        @decide (predicate value) (decidePredicate value)).length := by
  simp [countWhere, List.countP_eq_length_filter]

/-- Exact size of one fibre inside the supplied schedule.  Values outside the
schedule are deliberately irrelevant. -/
def fibreCount {α : Type u} {β : Type v} (schedule : Enumeration α)
    (label : α -> β) (target : β) (decEq : DecidableEq β) : Nat :=
  countWhere schedule (fun value => label value = target) (fun value => by
    exact @decEq (label value) target)

theorem fibreCount_le_card {α : Type u} {β : Type v}
    (schedule : Enumeration α) (label : α -> β) (target : β)
    (decEq : DecidableEq β) :
    fibreCount schedule label target decEq <= schedule.card :=
  countWhere_le_card _ _ _

/-- Exact visible checks: a hit at index `i` inspects `i + 1` entries; an
exhaustive miss inspects the entire schedule. -/
def executionChecks {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Search.Execution schedule predicate) :
    Nat :=
  match execution.hit? with
  | some hit => hit.index.1 + 1
  | none => schedule.card

@[simp] theorem executionChecks_of_hit {α : Type u}
    {schedule : Enumeration α} {predicate : α -> Prop}
    (execution : Search.Execution schedule predicate)
    (hit : Search.IndexedHit schedule predicate)
    (found : execution.hit? = some hit) :
    executionChecks execution = hit.index.1 + 1 := by
  simp [executionChecks, found]

@[simp] theorem executionChecks_of_miss {α : Type u}
    {schedule : Enumeration α} {predicate : α -> Prop}
    (execution : Search.Execution schedule predicate)
    (absent : execution.hit? = none) :
    executionChecks execution = schedule.card := by
  simp [executionChecks, absent]

/-- Every early-terminating execution remains bounded by the exact input
schedule cardinality. -/
theorem executionChecks_le_card {α : Type u}
    {schedule : Enumeration α} {predicate : α -> Prop}
    (execution : Search.Execution schedule predicate) :
    executionChecks execution <= schedule.card := by
  cases found : execution.hit? with
  | none => simp [executionChecks, found]
  | some hit =>
      simp only [executionChecks, found]
      omega

/-- Visible checks are determined exactly by the execution's observable first
index. -/
theorem executionChecks_eq_index? {α : Type u}
    {schedule : Enumeration α} {predicate : α -> Prop}
    (execution : Search.Execution schedule predicate) :
    executionChecks execution =
      match execution.index? with
      | some index => index + 1
      | none => schedule.card := by
  cases found : execution.hit? with
  | none => simp [executionChecks, Search.Execution.index?, found]
  | some hit => simp [executionChecks, Search.Execution.index?, found]

/-- Exact reference count, stated directly against Mathlib's deterministic
first-index computation. -/
theorem run_checks_eq_reference {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    executionChecks (Search.run schedule predicate decidePredicate) =
      match schedule.values.findIdx? (fun value =>
        @decide (predicate value) (decidePredicate value)) with
      | some index => index + 1
      | none => schedule.card := by
  rw [executionChecks_eq_index?, Search.run_index?_eq_findIdx?]
  rfl

/-- The canonical runner paired with its exact visible check count. -/
def countedRun {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    Counted (Search.Execution schedule predicate) :=
  let execution := Search.run schedule predicate decidePredicate
  ⟨execution, executionChecks execution⟩

@[simp] theorem countedRun_value {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    (countedRun schedule predicate decidePredicate).value =
      Search.run schedule predicate decidePredicate :=
  rfl

@[simp] theorem countedRun_checks {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    (countedRun schedule predicate decidePredicate).checks =
      executionChecks (Search.run schedule predicate decidePredicate) :=
  rfl

/-- A degree-one work budget whose `checks` field is the exact visible count
of each certified execution. -/
def firstHitWorkBudget {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop) :
    PolynomialCheckBudget (Search.Execution schedule predicate) where
  size := fun _execution => schedule.card
  checks := executionChecks
  coefficient := 1
  degree := 1
  bounded := by
    intro execution
    have bounded := executionChecks_le_card execution
    simp only [one_mul, pow_one]
    exact Nat.le_trans bounded (Nat.le_succ schedule.card)

@[simp] theorem firstHitWorkBudget_size {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (execution : Search.Execution schedule predicate) :
    (firstHitWorkBudget schedule predicate).size execution = schedule.card :=
  rfl

@[simp] theorem firstHitWorkBudget_checks {α : Type u}
    (schedule : Enumeration α) (predicate : α -> Prop)
    (execution : Search.Execution schedule predicate) :
    (firstHitWorkBudget schedule predicate).checks execution =
      executionChecks execution :=
  rfl

/-- Worst-case exhaustive work for a product schedule is the exact product of
the two input cardinalities. -/
theorem product_exhaustive_checks {α : Type u} {β : Type v}
    (left : Enumeration α) (right : Enumeration β) :
    (left.product right).card = left.card * right.card :=
  Enumeration.card_product left right

/-- Worst-case exhaustive work for a dependent schedule is the exact sum of
its residual-owned fibre cardinalities. -/
theorem dependent_exhaustive_checks {index : Type u}
    {fibre : index -> Type v}
    (schedule : DependentEnumeration index fibre) :
    schedule.flatten.card =
      (schedule.indices.values.map fun i => (schedule.fibres i).card).sum :=
  DependentEnumeration.card_flatten schedule

end Hypostructure.Core.Finite.Accounting
