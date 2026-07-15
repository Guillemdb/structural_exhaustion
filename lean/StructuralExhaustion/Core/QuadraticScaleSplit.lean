import Mathlib.Tactic

namespace StructuralExhaustion.Core.QuadraticScaleSplit

/-!
# Constant-work quadratic scale split

Many structural-exhaustion proofs branch on whether a nonnegative load is
larger than a fixed square-root scale.  Squaring the comparison gives an
exact natural-number decision and avoids real arithmetic or numerical
approximation.  This module owns that reusable branch contract.
-/

structure Input where
  load : Nat
  coefficient : Nat
  order : Nat
  deriving Repr, DecidableEq

inductive Decision (input : Input) : Type
  | large (strict : input.coefficient * input.order < input.load ^ 2)
  | bounded (bound : input.load ^ 2 ≤ input.coefficient * input.order)

def decide (input : Input) : Decision input := by
  by_cases large : input.coefficient * input.order < input.load ^ 2
  · exact .large large
  · exact .bounded (by omega)

theorem exhaustive (input : Input) :
    input.coefficient * input.order < input.load ^ 2 ∨
      input.load ^ 2 ≤ input.coefficient * input.order := by
  cases decide input with
  | large strict => exact Or.inl strict
  | bounded bound => exact Or.inr bound

def checks (_input : Input) : Nat := 1

theorem checks_eq_one (input : Input) : checks input = 1 := rfl

structure VerifiedStage (input : Input) : Type where
  decision : Decision input
  total : input.coefficient * input.order < input.load ^ 2 ∨
    input.load ^ 2 ≤ input.coefficient * input.order
  work : checks input = 1

def verifiedStage (input : Input) : VerifiedStage input where
  decision := decide input
  total := exhaustive input
  work := checks_eq_one input

end StructuralExhaustion.Core.QuadraticScaleSplit
