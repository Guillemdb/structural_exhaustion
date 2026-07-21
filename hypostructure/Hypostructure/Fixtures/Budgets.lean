import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Budget.Work

namespace Hypostructure.Fixtures.Budgets

open Hypostructure.Core

def naturalResource : ResourceBudget where
  Resource := Nat
  le := (· <= ·)
  leRefl := Nat.le_refl
  leTrans := Nat.le_trans
  zero := 0
  add := (· + ·)
  ceiling := id
  zeroLe := Nat.zero_le
  addMono := Nat.add_le_add
  addAssoc := Nat.add_assoc
  zeroAdd := Nat.zero_add
  addZero := Nat.add_zero

example : naturalResource.sum ([1, 2, 3] : List Nat) = (6 : Nat) := by
  rfl

example :
    naturalResource.sum ([1, 2] : List Nat) <=
      naturalResource.sum ([2, 4] : List Nat) := by
  change 3 <= 6
  decide

def leftWork : PolynomialCheckBudget Nat :=
  PolynomialCheckBudget.constant id 2

def rightWork : PolynomialCheckBudget Nat :=
  PolynomialCheckBudget.constant id 3

example : (PolynomialCheckBudget.add leftWork rightWork).checks 10 = 5 := rfl

example : (PolynomialCheckBudget.branch leftWork rightWork).checks 10 = 3 := rfl

example : (Counted.pure 7).checks = 0 := rfl

end Hypostructure.Fixtures.Budgets
