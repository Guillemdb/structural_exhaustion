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

end Counted

end StructuralExhaustion.Core
