import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteSearch

universe u v

/-! Constructive proof-carrying search over exact enumerator-derived lists. -/

/-- The result of exhaustive search over an exact finite universe. -/
inductive Result {α : Type u} (p : α → Prop) where
  | found (value : α) (holds : p value)
  | absent (none : ∀ value : α, ¬ p value)

namespace Result

def value? {α : Type u} {p : α → Prop} : Result p → Option α
  | .found value _ => some value
  | .absent _ => none

theorem value_sound {α : Type u} {p : α → Prop} (result : Result p)
    {value : α} (h : result.value? = some value) : p value := by
  cases result with
  | found witness holds =>
      simp only [value?] at h
      cases h
      exact holds
  | absent none =>
      simp only [value?] at h
      contradiction

theorem none_complete {α : Type u} {p : α → Prop} (result : Result p)
    (h : result.value? = none) : ∀ value : α, ¬ p value := by
  cases result with
  | found witness holds =>
      simp only [value?] at h
      contradiction
  | absent none => exact none

end Result

/-- Search evidence relative to an arbitrary finite list. -/
inductive ListResult {α : Type u} (xs : List α) (p : α → Prop) where
  | found (value : α) (member : value ∈ xs) (holds : p value)
  | absent (none : ∀ value : α, value ∈ xs → ¬ p value)

/-- Proof-carrying view of Mathlib's executable `List.find?`. -/
def onList {α : Type u} (xs : List α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value)) : ListResult xs p := by
  let predicate : α → Bool := fun value => @decide (p value) (decideP value)
  match found : xs.find? predicate with
  | some value =>
      have holds : @decide (p value) (decideP value) = true := by
        simpa [predicate] using (List.find?_some (p := predicate) found)
      exact .found value (List.mem_of_find?_eq_some found)
        (of_decide_eq_true holds)
  | none =>
      exact .absent fun value member holds => by
        have absent := (List.find?_eq_none.mp found) value member
        simp [predicate, decide_eq_true holds] at absent

/-- Exhaustive search over an explicit Mathlib finite enumeration. -/
def search {α : Type u} (enumeration : FinEnum α)
    (p : α → Prop) (decideP : ∀ value : α, Decidable (p value)) : Result p :=
  match onList enumeration.orderedValues p decideP with
  | .found value _ holds => .found value holds
  | .absent absentProof =>
      .absent fun value => absentProof value (enumeration.mem_orderedValues value)

theorem search_sound {α : Type u} (enumeration : FinEnum α)
    (p : α → Prop) (decideP : ∀ value : α, Decidable (p value))
    {value : α} (h : (search enumeration p decideP).value? = some value) :
    p value :=
  Result.value_sound _ h

theorem search_complete {α : Type u}
    (enumeration : FinEnum α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value))
    (existsWitness : ∃ value : α, p value) :
    ∃ value : α, (search enumeration p decideP).value? = some value ∧ p value := by
  cases result : search enumeration p decideP with
  | found value holds =>
      exact ⟨value, by simp [Result.value?], holds⟩
  | absent none =>
      obtain ⟨value, holds⟩ := existsWitness
      exact (none value holds).elim

theorem search_none_iff {α : Type u}
    (enumeration : FinEnum α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value)) :
    (search enumeration p decideP).value? = none ↔ ∀ value : α, ¬ p value := by
  constructor
  · exact Result.none_complete _
  · intro none
    cases result : search enumeration p decideP with
    | found value holds => exact (none value holds).elim
    | absent absent => simp [Result.value?]

/-- Two purported executions of the same exhaustive search are equal. -/
theorem search_deterministic {α : Type u}
    (enumeration : FinEnum α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value))
    (left right : Result p)
    (leftIsRun : left = search enumeration p decideP)
    (rightIsRun : right = search enumeration p decideP) : left = right :=
  leftIsRun.trans rightIsRun.symm

/-- A first-hit witness retains the exact prefix certified to contain no hit. -/
structure FirstHit {α : Type u} (xs : List α) (p : α → Prop) where
  before : List α
  value : α
  after : List α
  split : xs = before ++ value :: after
  holds : p value
  beforeAbsent : ∀ candidate : α, candidate ∈ before → ¬ p candidate

namespace FirstHit

theorem member {α : Type u} {xs : List α} {p : α → Prop}
    (hit : FirstHit xs p) : hit.value ∈ xs := by
  have membership : hit.value ∈ hit.before ++ hit.value :: hit.after := by simp
  exact Eq.mpr (congrArg (fun values => hit.value ∈ values) hit.split) membership

end FirstHit

/-- Ordered exhaustive search: either the first hit and its clean prefix, or
an absence proof for the whole list. -/
inductive FirstResult {α : Type u} (xs : List α) (p : α → Prop) where
  | found (hit : FirstHit xs p)
  | absent (none : ∀ value : α, value ∈ xs → ¬ p value)

namespace FirstResult

def value? {α : Type u} {xs : List α} {p : α → Prop} :
    FirstResult xs p → Option α
  | .found hit => some hit.value
  | .absent _ => none

def before? {α : Type u} {xs : List α} {p : α → Prop} :
    FirstResult xs p → Option (List α)
  | .found hit => some hit.before
  | .absent _ => none

def HasHit {α : Type u} {xs : List α} {p : α → Prop} :
    FirstResult xs p → Prop
  | .found _ => True
  | .absent _ => False

end FirstResult

/-- Proof-carrying first-hit view of Mathlib's executable `List.find?`. -/
def firstOnList {α : Type u} (xs : List α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value)) : FirstResult xs p := by
  let predicate : α → Bool := fun value => @decide (p value) (decideP value)
  match found : xs.findIdx? predicate with
  | some index =>
      have bound : index < xs.length :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
      have indexEq : xs.findIdx predicate = index :=
        (List.findIdx?_eq_some_iff_findIdx_eq.mp found).2
      have holdsBool : predicate xs[index] := by
        have foundValue := List.of_findIdx?_eq_some found
        simpa [List.getElem?_eq_getElem bound] using foundValue
      exact .found {
        before := xs.take index
        value := xs[index]
        after := xs.drop (index + 1)
        split := by
          rw [List.getElem_cons_drop bound, List.take_append_drop]
        holds := of_decide_eq_true (by simpa [predicate] using holdsBool)
        beforeAbsent := by
          intro candidate member candidateHolds
          have absent : predicate candidate = false := by
            have member' : candidate ∈ xs.take (xs.findIdx predicate) := by
              simpa [indexEq] using member
            exact List.false_of_mem_take_findIdx (p := predicate) member'
          simp [predicate, decide_eq_true candidateHolds] at absent
      }
  | none =>
      exact .absent fun value member holds => by
        have absent := (List.findIdx?_eq_none_iff.mp found) value member
        simp [predicate, decide_eq_true holds] at absent

/-- Ordered search over an explicit Mathlib finite enumeration. -/
def first {α : Type u} (enumeration : FinEnum α)
    (p : α → Prop) (decideP : ∀ value : α, Decidable (p value)) :
    FirstResult enumeration.orderedValues p :=
  firstOnList enumeration.orderedValues p decideP

/-- Ordered search is sound and exhaustive over the entire enumerated
universe. -/
theorem first_total {α : Type u} (enumeration : FinEnum α)
    (p : α → Prop) (decideP : ∀ value : α, Decidable (p value)) :
    match first enumeration p decideP with
    | .found hit => hit.value ∈ enumeration.orderedValues ∧ p hit.value
    | .absent _ => ∀ value : α, ¬ p value := by
  cases result : first enumeration p decideP with
  | found hit => exact ⟨hit.member, hit.holds⟩
  | absent absentProof =>
      exact fun value => absentProof value (enumeration.mem_orderedValues value)

/-- Every reported first hit satisfies the predicate and occurs in the source
list.  Its `beforeAbsent` field is the generic no-earlier-hit theorem. -/
theorem first_hit_sound {α : Type u} {xs : List α} {p : α → Prop}
    (hit : FirstHit xs p) : hit.value ∈ xs ∧ p hit.value :=
  ⟨hit.member, hit.holds⟩

theorem first_hit_no_earlier {α : Type u} {xs : List α} {p : α → Prop}
    (hit : FirstHit xs p) :
    ∀ candidate : α, candidate ∈ hit.before → ¬ p candidate :=
  hit.beforeAbsent

theorem first_complete {α : Type u}
    (enumeration : FinEnum α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value))
    (existsWitness : ∃ value : α, p value) :
    (first enumeration p decideP).HasHit := by
  cases result : first enumeration p decideP with
  | found hit => trivial
  | absent absentProof =>
      obtain ⟨value, holds⟩ := existsWitness
      exact absentProof value (enumeration.mem_orderedValues value) holds

/-- Ordered search is a pure function and therefore has a unique result. -/
theorem first_deterministic {α : Type u} (xs : List α) (p : α → Prop)
    (decideP : ∀ value : α, Decidable (p value))
    (left right : FirstResult xs p)
    (leftIsRun : left = firstOnList xs p decideP)
    (rightIsRun : right = firstOnList xs p decideP) : left = right :=
  leftIsRun.trans rightIsRun.symm

/-- The certificate-producing runner selects the value at Mathlib's canonical
first satisfying index. -/
theorem firstOnList_value?_eq_findIdx? {α : Type u} (xs : List α)
    (p : α → Prop) (decideP : ∀ value : α, Decidable (p value)) :
    (firstOnList xs p decideP).value? =
      (xs.findIdx? fun value => @decide (p value) (decideP value)).bind
        (fun index => xs[index]?) := by
  unfold firstOnList
  dsimp only
  split
  · rename_i index found
    have bound : index < xs.length :=
      (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
    simp [FirstResult.value?, found, List.getElem?_eq_getElem bound]
  · rename_i found
    simp [FirstResult.value?, found]

/-- The selected first value is independent of the implementation of the
predicate's decision procedure. -/
theorem first_value_independent {α : Type u} (xs : List α) (p : α → Prop)
    (leftDecision rightDecision : ∀ value : α, Decidable (p value)) :
    (firstOnList xs p leftDecision).value? =
      (firstOnList xs p rightDecision).value? := by
  have decisions :
      (fun value => @decide (p value) (leftDecision value)) =
        (fun value => @decide (p value) (rightDecision value)) := by
    funext value
    exact decide_eq_decide.mpr Iff.rfl
  rw [firstOnList_value?_eq_findIdx?, firstOnList_value?_eq_findIdx?, decisions]

/-- Dependent exhaustive-search result.  The witness is constructed directly
in `Type`; it is never extracted from a propositional existential. -/
inductive DependentResult {ι : Type u} {α : ι → Type v}
    (p : (i : ι) → α i → Prop) where
  | found (index : ι) (value : α index) (holds : p index value)
  | absent (none : ∀ index : ι, ∀ value : α index, ¬ p index value)

namespace DependentResult

def index? {ι : Type u} {α : ι → Type v} {p : (i : ι) → α i → Prop} :
    DependentResult p → Option ι
  | .found index _ _ => some index
  | .absent _ => none

end DependentResult

private inductive DependentListResult {ι : Type u} {α : ι → Type v}
    (indices : List ι) (p : (i : ι) → α i → Prop) where
  | found (index : ι) (member : index ∈ indices)
      (value : α index) (holds : p index value)
  | absent (none : ∀ index : ι, index ∈ indices →
      ∀ value : α index, ¬ p index value)

private def dependentOnList {ι : Type u} {α : ι → Type v}
    (indices : List ι) (fibres : (i : ι) → FinEnum (α i))
    (p : (i : ι) → α i → Prop)
    (decideP : ∀ index value, Decidable (p index value)) :
    DependentListResult indices p :=
  match indices with
  | [] => .absent (by
      intro index member
      cases member)
  | head :: tail =>
      match search (fibres head) (p head) (decideP head) with
      | .found value holds => .found head (by simp) value holds
      | .absent headAbsent =>
          match dependentOnList tail fibres p decideP with
          | .found index member value holds =>
              .found index (List.mem_cons_of_mem head member) value holds
          | .absent tailAbsent => .absent (by
              intro index member value
              simp only [List.mem_cons] at member
              cases member with
              | inl equal =>
                  subst index
                  exact headAbsent value
              | inr inTail => exact tailAbsent index inTail value)

/-- Exhaustive nested search over a finite index enumeration and an exact
finite enumeration for each dependent fibre. -/
def dependentSearch {ι : Type u} {α : ι → Type v}
    (enumeration : Core.DependentEnumeration ι α)
    (p : (i : ι) → α i → Prop)
    (decideP : ∀ index value, Decidable (p index value)) :
    DependentResult p :=
  match dependentOnList enumeration.indices.orderedValues enumeration.fibres p decideP with
  | .found index _ value holds => .found index value holds
  | .absent absentProof => .absent fun index =>
      absentProof index (enumeration.indices.mem_orderedValues index)

theorem dependentSearch_sound {ι : Type u} {α : ι → Type v}
    (enumeration : Core.DependentEnumeration ι α)
    (p : (i : ι) → α i → Prop)
    (decideP : ∀ index value, Decidable (p index value)) :
    match dependentSearch enumeration p decideP with
    | .found index value _ => p index value
    | .absent _ => True := by
  cases dependentSearch enumeration p decideP with
  | found index value holds => exact holds
  | absent none => trivial

theorem dependentSearch_complete {ι : Type u} {α : ι → Type v}
    (enumeration : Core.DependentEnumeration ι α)
    (p : (i : ι) → α i → Prop)
    (decideP : ∀ index value, Decidable (p index value))
    (existsWitness : ∃ index : ι, ∃ value : α index, p index value) :
    match dependentSearch enumeration p decideP with
    | .found _ _ _ => True
    | .absent _ => False := by
  cases result : dependentSearch enumeration p decideP with
  | found index value holds => trivial
  | absent none =>
      obtain ⟨index, value, holds⟩ := existsWitness
      exact none index value holds

theorem dependentSearch_deterministic {ι : Type u} {α : ι → Type v}
    (enumeration : Core.DependentEnumeration ι α)
    (p : (i : ι) → α i → Prop)
    (decideP : ∀ index value, Decidable (p index value))
    (left right : DependentResult p)
    (leftIsRun : left = dependentSearch enumeration p decideP)
    (rightIsRun : right = dependentSearch enumeration p decideP) : left = right :=
  leftIsRun.trans rightIsRun.symm

/-- Optional optimized execution, checked against a reference semantic
predicate.  Optimization cannot change the meaning of the reference runner. -/
structure OptimizedSearch (Input : Type u) (Output : Input → Type v)
    (Valid : (input : Input) → Output input → Prop)
    (ReferenceHasResult : Input → Prop) where
  run : (input : Input) → Option (Output input)
  sound : ∀ input result, run input = some result → Valid input result
  complete : ∀ input, ReferenceHasResult input → ∃ result, run input = some result

end StructuralExhaustion.Core.FiniteSearch
