import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core

universe u

/-! Canonical executable truth values and exact finite response comparison. -/

/-- Evaluate a proposition with an explicitly supplied decision procedure. -/
def truthValue (p : Prop) (decision : Decidable p) : Bool :=
  @decide p decision

theorem truthValue_eq_true_iff (p : Prop) (decision : Decidable p) :
    truthValue p decision = true ↔ p := by
  exact @decide_eq_true_iff p decision

theorem truthValue_eq_false_iff (p : Prop) (decision : Decidable p) :
    truthValue p decision = false ↔ ¬ p := by
  exact @decide_eq_false_iff_not p decision

/-- The reference observation used by replacement and context comparison. -/
structure ExactObservation where
  baseline : Bool
  target : Bool
  deriving Repr, DecidableEq

namespace ExactObservation

/-- Compute the exact baseline/target truth pair for one object. -/
def ofPredicates (Baseline Target : Prop)
    (baselineDecision : Decidable Baseline)
    (targetDecision : Decidable Target) : ExactObservation where
  baseline := truthValue Baseline baselineDecision
  target := truthValue Target targetDecision

theorem baseline_eq_true_iff (Baseline Target : Prop)
    (baselineDecision : Decidable Baseline)
    (targetDecision : Decidable Target) :
    (ofPredicates Baseline Target baselineDecision targetDecision).baseline = true ↔
      Baseline :=
  truthValue_eq_true_iff Baseline baselineDecision

theorem target_eq_true_iff (Baseline Target : Prop)
    (baselineDecision : Decidable Baseline)
    (targetDecision : Decidable Target) :
    (ofPredicates Baseline Target baselineDecision targetDecision).target = true ↔
      Target :=
  truthValue_eq_true_iff Target targetDecision

end ExactObservation

/-- Exact comparison of two response functions over a finite context
universe. -/
inductive ResponseComparison {Context : Type u}
    (left right : Context → Bool) where
  | equal (allEqual : ∀ context, left context = right context)
  | different (context : Context) (differs : left context ≠ right context)

namespace ResponseComparison

/-- Compare two responses by searching for their first differing context. -/
def compare {Context : Type u} (contexts : FinEnum Context)
    (left right : Context → Bool) : ResponseComparison left right :=
  match FiniteSearch.search contexts (fun context => left context ≠ right context)
      (fun _ => inferInstance) with
  | .found context differs => .different context differs
  | .absent noDifference => .equal fun context =>
      match decEq (left context) (right context) with
      | .isTrue same => same
      | .isFalse differs => (noDifference context differs).elim

theorem equal_sound {Context : Type u} {left right : Context → Bool}
    (allEqual : ∀ context, left context = right context) :
    ∀ context, left context = right context :=
  allEqual

theorem different_sound {Context : Type u} {left right : Context → Bool}
    (context : Context) (differs : left context ≠ right context) :
    left context ≠ right context :=
  differs

theorem compare_total {Context : Type u} (contexts : FinEnum Context)
    (left right : Context → Bool) :
    (∀ context, left context = right context) ∨
      ∃ context, left context ≠ right context := by
  cases compare contexts left right with
  | equal allEqual => exact Or.inl allEqual
  | different context differs => exact Or.inr ⟨context, differs⟩

end ResponseComparison

end StructuralExhaustion.Core
