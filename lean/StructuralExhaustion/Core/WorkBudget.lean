namespace StructuralExhaustion.Core

universe u v

/-!
# Verified local-work budgets

Structural-exhaustion runners count calls to their primitive local predicates.
The count deliberately does not model kernel proof checking or the internal
implementation of an application primitive.  It records the finite inspection
schedule owned by the framework.
-/

/-- A uniform polynomial upper bound for a family of primitive-check counts. -/
structure PolynomialCheckBudget (Input : Type u) where
  size : Input → Nat
  checks : Input → Nat
  coefficient : Nat
  degree : Nat
  bounded : ∀ input,
    checks input ≤ coefficient * (size input + 1) ^ degree

namespace PolynomialCheckBudget

/-- A constant local schedule is a degree-zero polynomial schedule. -/
def constant {Input : Type u} (size : Input → Nat) (checks : Nat) :
    PolynomialCheckBudget Input where
  size := size
  checks := fun _ => checks
  coefficient := checks
  degree := 0
  bounded := by simp

/-- Reindex a verified work schedule along an input adapter. -/
def comap {Input : Type u} {Next : Type v}
    (budget : PolynomialCheckBudget Input) (adapter : Next → Input) :
    PolynomialCheckBudget Next where
  size := fun input => budget.size (adapter input)
  checks := fun input => budget.checks (adapter input)
  coefficient := budget.coefficient
  degree := budget.degree
  bounded := fun input => budget.bounded (adapter input)

/-- Repeat every primitive check in a verified schedule a fixed number of
times. -/
def scale {Input : Type u} (factor : Nat)
    (budget : PolynomialCheckBudget Input) :
    PolynomialCheckBudget Input where
  size := budget.size
  checks := fun input => factor * budget.checks input
  coefficient := factor * budget.coefficient
  degree := budget.degree
  bounded := by
    intro input
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left factor (budget.bounded input)

private theorem term_le_commonEnvelope {Input : Type u}
    (budget other : PolynomialCheckBudget Input) (input : Input) :
    budget.coefficient * (budget.size input + 1) ^ budget.degree ≤
      budget.coefficient *
        (max (budget.size input) (other.size input) + 1) ^
          max budget.degree other.degree := by
  apply Nat.mul_le_mul_left
  calc
    (budget.size input + 1) ^ budget.degree ≤
        (max (budget.size input) (other.size input) + 1) ^
          budget.degree :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_max_left _ _) 1) _
    _ ≤ (max (budget.size input) (other.size input) + 1) ^
          max budget.degree other.degree :=
      Nat.pow_le_pow_right (Nat.succ_pos _)
        (Nat.le_max_left _ _)

/-- Sequential composition of two verified schedules.  The framework chooses
one common polynomial envelope; applications only compose schedules. -/
def add {Input : Type u}
    (left right : PolynomialCheckBudget Input) :
    PolynomialCheckBudget Input where
  size := fun input => max (left.size input) (right.size input)
  checks := fun input => left.checks input + right.checks input
  coefficient := left.coefficient + right.coefficient
  degree := max left.degree right.degree
  bounded := by
    intro input
    calc
      left.checks input + right.checks input ≤
          left.coefficient * (left.size input + 1) ^ left.degree +
            right.coefficient * (right.size input + 1) ^ right.degree :=
        Nat.add_le_add (left.bounded input) (right.bounded input)
      _ ≤ left.coefficient *
              (max (left.size input) (right.size input) + 1) ^
                max left.degree right.degree +
            right.coefficient *
              (max (left.size input) (right.size input) + 1) ^
                max left.degree right.degree :=
        Nat.add_le_add
          (term_le_commonEnvelope left right input)
          (by
            simpa [Nat.max_comm] using
              term_le_commonEnvelope right left input)
      _ = (left.coefficient + right.coefficient) *
            (max (left.size input) (right.size input) + 1) ^
              max left.degree right.degree := by
        rw [Nat.add_mul]

/-- Mutually exclusive branch composition.  Its exact check count is the
larger branch count while its polynomial envelope is framework-composed. -/
def branch {Input : Type u}
    (left right : PolynomialCheckBudget Input) :
    PolynomialCheckBudget Input :=
  let combined := add left right
  { combined with
    checks := fun input => max (left.checks input) (right.checks input)
    bounded := by
      intro input
      exact Nat.le_trans ((Nat.max_le).2 ⟨
        Nat.le_add_right _ _,
        Nat.le_add_left _ _⟩) (combined.bounded input) }

end PolynomialCheckBudget

/-- A computed value paired with the number of primitive local checks used to
produce it. -/
structure Counted (Output : Type v) where
  value : Output
  checks : Nat

namespace Counted

def pure {Output : Type v} (value : Output) : Counted Output :=
  ⟨value, 0⟩

def map {Output : Type v} {Next : Type u} (f : Output → Next)
    (result : Counted Output) : Counted Next :=
  ⟨f result.value, result.checks⟩

/-- Sequential counted computation; primitive checks add exactly. -/
def bind {Output : Type v} {Next : Type u} (result : Counted Output)
    (next : Output → Counted Next) : Counted Next :=
  let continuation := next result.value
  ⟨continuation.value, result.checks + continuation.checks⟩

/-- Pair two counted results and add their exact check counts. -/
def zip {Left : Type u} {Right : Type v}
    (left : Counted Left) (right : Counted Right) :
    Counted (Left × Right) :=
  ⟨(left.value, right.value), left.checks + right.checks⟩

end Counted

end StructuralExhaustion.Core
