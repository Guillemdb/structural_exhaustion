import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Decision

/-!
# Deterministic proof-carrying finite search

Search inspects only an explicit `Enumeration`.  The reference runner records
the canonical first satisfying index and proves that its prefix is clean; if
there is no hit it proves avoidance at every exact schedule index.

The execution constructor is private.  Downstream CTs consume its fields or
the framework-owned residual decision returned by `route`; applications do
not choose search or routing constructors.
-/

namespace Hypostructure.Core.Finite.Search

open Hypostructure.Core.Finite

universe u

/-- A canonical first hit at an exact schedule index. -/
structure IndexedHit {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop) where
  private mk ::
  index : Fin schedule.card
  holds : predicate (schedule.get index)
  beforeAbsent : forall candidate,
    candidate ∈ schedule.values.take index.1 -> Not (predicate candidate)

namespace IndexedHit

/-- The selected value is computed from the retained exact index. -/
def value {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (hit : IndexedHit schedule predicate) : α :=
  schedule.get hit.index

theorem member {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (hit : IndexedHit schedule predicate) :
    hit.value ∈ schedule.values :=
  schedule.get_mem hit.index

theorem sound {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (hit : IndexedHit schedule predicate) :
    predicate hit.value :=
  hit.holds

/-- No scheduled member in the exact prefix before the hit can satisfy the
predicate. -/
theorem first {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (hit : IndexedHit schedule predicate) :
    forall candidate,
      candidate ∈ schedule.values.take hit.index.1 ->
        Not (predicate candidate) :=
  hit.beforeAbsent

end IndexedHit

/-- Exhaustive avoidance over every exact schedule index. -/
def Avoids {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop) : Prop :=
  forall index : Fin schedule.card, Not (predicate (schedule.get index))

/-- Framework-produced result of one canonical first-hit scan. -/
structure Execution {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop) where
  private mk ::
  hit? : Option (IndexedHit schedule predicate)
  exhaustive : hit? = none -> Avoids schedule predicate

namespace Execution

/-- Observable selected index, if any. -/
def index? {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate) :
    Option Nat :=
  execution.hit?.map fun hit => hit.index.1

/-- Observable selected value, if any. -/
def value? {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate) :
    Option α :=
  execution.hit?.map IndexedHit.value

/-- The executable branch proposition used by Core residual routing. -/
def HasHit {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate) : Prop :=
  execution.hit?.isSome = true

instance instDecidableHasHit {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate) :
    Decidable execution.HasHit := by
  unfold HasHit
  infer_instance

theorem hasHit_of_eq_some {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate)
    {hit : IndexedHit schedule predicate}
    (equal : execution.hit? = some hit) : execution.HasHit := by
  simp [HasHit, equal]

/-- Recover the exact indexed certificate from the executable yes branch. -/
def hitOfHasHit {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate)
    (hasHit : execution.HasHit) : IndexedHit schedule predicate := by
  cases found : execution.hit? with
  | none => simp [HasHit, found] at hasHit
  | some hit => exact hit

/-- The complementary branch is derived from the execution certificate, not
authored by the caller. -/
theorem avoids_of_not_hasHit {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate)
    (absent : Not execution.HasHit) : Avoids schedule predicate := by
  cases found : execution.hit? with
  | none => exact execution.exhaustive found
  | some hit => exact (absent (by simp [HasHit, found])).elim

theorem hit_or_avoids {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate) :
    execution.HasHit ∨ Avoids schedule predicate := by
  cases found : execution.hit? with
  | none => exact Or.inr (execution.exhaustive found)
  | some hit => exact Or.inl (by simp [HasHit, found])

end Execution

/-- Boolean view used by the deterministic Mathlib reference scan. -/
def booleanPredicate {α : Type u} (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    α -> Bool :=
  fun value => @decide (predicate value) (decidePredicate value)

/-- Canonical left-to-right first-hit scan over the exact supplied schedule. -/
def run {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    Execution schedule predicate := by
  let test := booleanPredicate predicate decidePredicate
  match found : schedule.values.findIdx? test with
  | some index =>
      have bound : index < schedule.values.length :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
      have indexEq : schedule.values.findIdx test = index :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp found).2
      have holdsBool : test schedule.values[index] := by
        have foundValue := List.of_findIdx?_eq_some found
        simpa [List.getElem?_eq_getElem bound] using foundValue
      exact .mk (some {
        index := ⟨index, by simpa [Enumeration.card] using bound⟩
        holds := by
          change predicate schedule.values[index]
          exact of_decide_eq_true (by
            simpa [test, booleanPredicate] using holdsBool)
        beforeAbsent := by
          intro candidate member candidateHolds
          have falseAtCandidate : test candidate = false := by
            have inCleanPrefix :
                candidate ∈ schedule.values.take
                  (schedule.values.findIdx test) := by
              simpa [indexEq] using member
            exact List.false_of_mem_take_findIdx
              (p := test) inCleanPrefix
          simp [test, booleanPredicate,
            decide_eq_true candidateHolds] at falseAtCandidate
      }) (by simp)
  | none =>
      exact .mk none (by
        intro _equal index holds
        have absentAtValue :=
          (List.findIdx?_eq_none_iff.mp found)
            (schedule.get index) (schedule.get_mem index)
        simp [test, booleanPredicate, decide_eq_true holds] at absentAtValue)

/-- Mathlib's `findIdx?` is the deterministic reference semantics of the
observable selected index. -/
theorem run_index?_eq_findIdx? {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    (run schedule predicate decidePredicate).index? =
      schedule.values.findIdx?
        (booleanPredicate predicate decidePredicate) := by
  simp only [run, Execution.index?]
  split <;> simp_all

/-- Any reported value is an exact schedule member satisfying the predicate. -/
theorem value_sound {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    {value : α}
    (reported : (run schedule predicate decidePredicate).value? = some value) :
    value ∈ schedule.values ∧ predicate value := by
  unfold Execution.value? at reported
  cases found : (run schedule predicate decidePredicate).hit? with
  | none => simp [found] at reported
  | some hit =>
      simp only [found, Option.map_some, Option.some.injEq] at reported
      subst value
      exact ⟨hit.member, hit.sound⟩

/-- An exhaustive miss is equivalent to avoidance of every exact scheduled
member; no claim is made about values outside the supplied family. -/
theorem hit?_eq_none_iff {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value)) :
    (run schedule predicate decidePredicate).hit? = none ↔
      forall value, value ∈ schedule.values -> Not (predicate value) := by
  constructor
  · intro absent value member holds
    have avoids := (run schedule predicate decidePredicate).exhaustive absent
    obtain ⟨index, equal⟩ :=
      (schedule.mem_iff_exists_index value).mp member
    exact avoids index (by simpa [equal] using holds)
  · intro avoids
    cases found : (run schedule predicate decidePredicate).hit? with
    | none => rfl
    | some hit =>
        exact (avoids hit.value hit.member hit.sound).elim

/-- A witness inside the exact supplied family forces the hit branch. -/
theorem complete {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (existsWitness : Exists fun value =>
      value ∈ schedule.values ∧ predicate value) :
    (run schedule predicate decidePredicate).HasHit := by
  cases found : (run schedule predicate decidePredicate).hit? with
  | some hit => simp [Execution.HasHit, found]
  | none =>
      obtain ⟨value, member, holds⟩ := existsWitness
      have avoids := (run schedule predicate decidePredicate).exhaustive found
      obtain ⟨index, equal⟩ :=
        (schedule.mem_iff_exists_index value).mp member
      exact (avoids index (by simpa [equal] using holds)).elim

/-- Two claimed executions of the same pure reference runner coincide. -/
theorem deterministic {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop)
    (decidePredicate : (value : α) -> Decidable (predicate value))
    (left right : Execution schedule predicate)
    (leftIsRun : left = run schedule predicate decidePredicate)
    (rightIsRun : right = run schedule predicate decidePredicate) :
    left = right :=
  leftIsRun.trans rightIsRun.symm

/-- The Core decision node for a search execution.  It derives exhaustive
avoidance from the negation of the executable hit tag. -/
def decisionNode {α : Type u} (schedule : Enumeration α)
    (predicate : α -> Prop) :
    Residual.Decision.Node (Execution schedule predicate)
      (fun execution => execution.HasHit)
      (fun _execution => Avoids schedule predicate) :=
  Residual.Decision.Node.create
    (fun execution => Execution.instDecidableHasHit execution)
    (fun execution absent => execution.avoids_of_not_hasHit absent)

/-- Route a completed scan through the framework-owned residual decision API.
Applications cannot select either constructor. -/
def route {α : Type u} {schedule : Enumeration α}
    {predicate : α -> Prop} (execution : Execution schedule predicate) :
    Residual.Decision.Stage
      (fun result : Execution schedule predicate => result.HasHit)
      (fun _result : Execution schedule predicate => Avoids schedule predicate) :=
  (decisionNode schedule predicate).run execution

@[simp] theorem route_previous {α : Type u}
    {schedule : Enumeration α} {predicate : α -> Prop}
    (execution : Execution schedule predicate) :
    (route execution).previous = execution :=
  rfl

/-- Dependent search is ordinary Core search over the exact flattened
index-major schedule. -/
def runDependent {index : Type u} {fibre : index -> Type u}
    (schedule : DependentEnumeration index fibre)
    (predicate : (i : index) -> fibre i -> Prop)
    (decidePredicate : (i : index) -> (value : fibre i) ->
      Decidable (predicate i value)) :
    Execution schedule.flatten (fun value => predicate value.1 value.2) :=
  run schedule.flatten (fun value => predicate value.1 value.2)
    (fun value => decidePredicate value.1 value.2)

end Hypostructure.Core.Finite.Search
