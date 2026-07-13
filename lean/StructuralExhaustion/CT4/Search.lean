import StructuralExhaustion.CT4.State

namespace StructuralExhaustion.CT4

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

private def assignedNoneDecidable (assigned : Option S.Payer) :
    Decidable (assigned = none) :=
  match assigned with
  | none => .isTrue rfl
  | some _ => .isFalse (by intro equality; cases equality)

def assignmentState : AssignmentState S capability input :=
  {
    assigned := assignedPayer S capability input
    exact := fun _ => rfl
    sound := assignedPayer_sound S capability input
    noneComplete := by
      intro demand assignedNone payer eligible
      unfold assignedPayer at assignedNone
      cases result : Core.FiniteSearch.search capability.payers
          (S.Eligible input demand)
          (capability.eligibleDecidable input demand) with
      | found foundPayer foundEligible =>
          simp [result, Core.FiniteSearch.Result.value?] at assignedNone
      | absent noEligible => exact noEligible payer eligible
  }

inductive AvailabilityDecision where
  | missing (residual : MissingPayerResidual S input)
  | total (state : TotalAssignmentState S capability input)

def analyzeAvailability (assignment : AssignmentState S capability input) :
    AvailabilityDecision S capability input :=
  match Core.FiniteSearch.search capability.demands
      (fun demand => assignment.assigned demand = none)
      (fun demand => assignedNoneDecidable S
        (assignment.assigned demand)) with
  | .found demand assignedNone =>
      .missing ⟨demand, assignment.noneComplete demand assignedNone⟩
  | .absent noMissing => .total {
      assignment := assignment
      total := fun demand => by
        cases assigned : assignment.assigned demand with
        | none => exact (noMissing demand assigned).elim
        | some payer =>
            have eligible := assignment.sound demand payer assigned
            exact ⟨payer, rfl, eligible⟩
    }

def overloadedDecidable (total : TotalAssignmentState S capability input)
    (payer : S.Payer) :
    Decidable (Overloaded S capability input total.assignment payer) :=
  Nat.decLt _ _

inductive FibreDecision (total : TotalAssignmentState S capability input) where
  | overloaded (residual : OverloadedFibreResidual S capability input)
  | bounded (state : BoundedFibreState S capability input)

def analyzeFibres (total : TotalAssignmentState S capability input) :
    FibreDecision S capability input total :=
  match Core.FiniteSearch.search capability.payers
      (Overloaded S capability input total.assignment)
      (overloadedDecidable S capability input total) with
  | .found payer overloaded => .overloaded ⟨total, payer, overloaded⟩
  | .absent noOverload => .bounded {
      total := total
      bounded := fun payer => Nat.le_of_not_gt (noOverload payer)
    }

inductive CapacityDecision (bounded : BoundedFibreState S capability input) where
  | closes (certificate : C4Certificate S capability input)
  | residual (residual : CapacityResidual S capability input)

def compareCapacity (bounded : BoundedFibreState S capability input) :
    CapacityDecision S capability input bounded :=
  match Nat.decLt (totalCapacity S capability input)
      (capability.required input) with
  | .isTrue less => .closes ⟨bounded, less⟩
  | .isFalse notLess => .residual ⟨bounded, Nat.le_of_not_gt notLess⟩

end StructuralExhaustion.CT4
