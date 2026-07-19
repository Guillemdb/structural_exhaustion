import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Examples.WorkBudget

open StructuralExhaustion

def first : Core.PolynomialCheckBudget Nat :=
  Core.PolynomialCheckBudget.constant id 2

def second : Core.PolynomialCheckBudget Nat :=
  Core.PolynomialCheckBudget.constant id 3

def sequential := first.add second
def alternative := first.branch second

example (input : Nat) : sequential.checks input = 5 := rfl
example (input : Nat) : alternative.checks input = 3 := rfl
example (input : Nat) :
    sequential.checks input ≤ sequential.coefficient *
      (sequential.size input + 1) ^ sequential.degree :=
  sequential.bounded input

def counted : Core.Counted Nat :=
  (Core.Counted.pure 2).bind fun value => ⟨value + 1, 4⟩

example : counted.value = 3 := rfl
example : counted.checks = 4 := rfl

end StructuralExhaustion.Examples.WorkBudget
