import Mathlib.Tactic
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FinitePriorityOptionScanWork

universe u v

/-!
# Work accounting for an option-first finite classifier

The classifier first checks one already supplied optional witness.  Only when
that check is negative does it scan one declared finite code schedule.  This
module accounts for that schedule; it does not enumerate the type represented
by the codes.
-/

inductive Step where
  | optionalWitness
  | finiteCodeScan
  deriving DecidableEq, Repr

def trace {Hit : Type u} (hit? : Option Hit) : List Step :=
  match hit? with
  | some _ => [.optionalWitness]
  | none => [.optionalWitness, .finiteCodeScan]

def checks {Hit : Type u} {Code : Type v}
    (hit? : Option Hit) (codes : FinEnum Code) : Nat :=
  match hit? with
  | some _ => 1
  | none => 1 + codes.card

@[simp] theorem trace_some {Hit : Type u} (hit : Hit) :
    trace (some hit) = [.optionalWitness] := rfl

@[simp] theorem trace_none {Hit : Type u} :
    trace (none : Option Hit) = [.optionalWitness, .finiteCodeScan] := rfl

@[simp] theorem checks_some {Hit : Type u} {Code : Type v}
    (hit : Hit) (codes : FinEnum Code) :
    checks (some hit) codes = 1 := rfl

@[simp] theorem checks_none {Hit : Type u} {Code : Type v}
    (codes : FinEnum Code) :
    checks (none : Option Hit) codes = 1 + codes.card := rfl

/-- The complete option-first classifier performs at most one optional check
plus one pass over the actual declared code schedule. -/
theorem checks_le_codes_add_one {Hit : Type u} {Code : Type v}
    (hit? : Option Hit) (codes : FinEnum Code) :
    checks hit? codes ≤ codes.card + 1 := by
  cases hit? <;> simp [checks, Nat.add_comm]

/-- A tiny polynomial presentation of the same local bound. -/
theorem checks_linear {Hit : Type u} {Code : Type v}
    (hit? : Option Hit) (codes : FinEnum Code) :
    checks hit? codes ≤ 2 * (codes.card + 1) := by
  have bound := checks_le_codes_add_one hit? codes
  omega

end StructuralExhaustion.Core.FinitePriorityOptionScanWork
