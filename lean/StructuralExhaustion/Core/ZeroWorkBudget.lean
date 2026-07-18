import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Core.PolynomialCheckBudget

universe u

/-- A proof-only projection or handoff performs no primitive inspection.  The
linear envelope is deliberately nonzero, so downstream code may use one
uniform polynomial shape without rebuilding an arithmetic proof. -/
def zero {Input : Type u} (size : Input → Nat) :
    PolynomialCheckBudget Input where
  size := size
  checks := fun _ => 0
  coefficient := 1
  degree := 1
  bounded := by simp

end StructuralExhaustion.Core.PolynomialCheckBudget
