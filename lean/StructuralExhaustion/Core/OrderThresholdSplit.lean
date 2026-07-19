import Mathlib.Order.Defs.LinearOrder
import StructuralExhaustion.Core.ZeroWorkBudget

namespace StructuralExhaustion.Core.OrderThresholdSplit

/-!
# Proof-level ordered threshold splits

This profile owns the exhaustive dichotomy `threshold ≤ value` or
`value < threshold` for any linear order.  It is a logical branch constructor,
not an evaluator: applications may use symbolic real-valued quantities without
normalizing or computing them.
-/

universe u

structure Profile (α : Type u) [LinearOrder α] where
  value : α
  threshold : α

namespace Profile

variable {α : Type u} [LinearOrder α]

inductive Outcome (profile : Profile α) : Type
  | high (bound : profile.threshold ≤ profile.value)
  | low (strict : profile.value < profile.threshold)

def run (profile : Profile α) : profile.Outcome :=
  if high : profile.threshold ≤ profile.value then
    .high high
  else
    .low (lt_of_not_ge high)

theorem exhaustive (profile : Profile α) :
    profile.threshold ≤ profile.value ∨ profile.value < profile.threshold :=
  le_or_gt profile.threshold profile.value

/-- A proof-level threshold split performs no primitive finite inspection. -/
def workBudget (_profile : Profile α) : PolynomialCheckBudget Unit :=
  PolynomialCheckBudget.zero (fun _ => 0)

@[simp] theorem checks_eq_zero (profile : Profile α) :
    profile.workBudget.checks () = 0 :=
  rfl

structure VerifiedStage (profile : Profile α) : Type where
  outcome : profile.Outcome
  total : profile.threshold ≤ profile.value ∨ profile.value < profile.threshold
  work : profile.workBudget.checks () = 0

def verifiedStage (profile : Profile α) : profile.VerifiedStage where
  outcome := profile.run
  total := profile.exhaustive
  work := profile.checks_eq_zero

end Profile

end StructuralExhaustion.Core.OrderThresholdSplit
