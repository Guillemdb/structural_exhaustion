import StructuralExhaustion.CT4.Capability

namespace StructuralExhaustion.CT4

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (input : Input P)

def assignedPayer (demand : S.Demand) : Option S.Payer :=
  (Core.FiniteSearch.search capability.payers (S.Eligible input demand)
    (capability.eligibleDecidable input demand)).value?

theorem assignedPayer_sound (demand : S.Demand) (payer : S.Payer)
    (assigned : assignedPayer S capability input demand = some payer) :
    S.Eligible input demand payer :=
  Core.FiniteSearch.search_sound capability.payers (S.Eligible input demand)
    (capability.eligibleDecidable input demand) assigned

def MissingAt (demand : S.Demand) : Prop :=
  ∀ payer : S.Payer, ¬ S.Eligible input demand payer

/-- Framework-computed canonical assignment table.  The search is performed
once at this node; downstream nodes consume `assigned` and its exactness
proofs rather than re-running payer search. -/
structure AssignmentState where
  assigned : S.Demand → Option S.Payer
  exact : ∀ demand,
    assigned demand = assignedPayer S capability input demand
  sound : ∀ demand payer,
    assigned demand = some payer → S.Eligible input demand payer
  noneComplete : ∀ demand,
    assigned demand = none → MissingAt S input demand

structure MissingPayerResidual where
  demand : S.Demand
  noEligible : MissingAt S input demand

structure TotalAssignmentState where
  assignment : AssignmentState S capability input
  total : ∀ demand, ∃ payer,
    assignment.assigned demand = some payer ∧
      S.Eligible input demand payer

def samePayer (assigned : Option S.Payer) (payer : S.Payer) : Bool :=
  match assigned with
  | none => false
  | some candidate => @decide (candidate = payer)
      (capability.payers.decEq candidate payer)

def fibre (assignment : AssignmentState S capability input)
    (payer : S.Payer) : List S.Demand :=
  capability.demands.orderedValues.filter fun demand =>
    samePayer S capability (assignment.assigned demand) payer

def fibreWeight (assignment : AssignmentState S capability input)
    (payer : S.Payer) : Nat :=
  (fibre S capability input assignment payer).foldl
    (fun total demand => total + S.demandWeight input demand) 0

def Overloaded (assignment : AssignmentState S capability input)
    (payer : S.Payer) : Prop :=
  S.capacity input payer <
    fibreWeight S capability input assignment payer

structure OverloadedFibreResidual where
  total : TotalAssignmentState S capability input
  payer : S.Payer
  overloaded : Overloaded S capability input total.assignment payer

structure BoundedFibreState where
  total : TotalAssignmentState S capability input
  bounded : ∀ payer,
    fibreWeight S capability input total.assignment payer ≤
      S.capacity input payer

def totalCapacity : Nat := capability.payers.orderedValues.foldl
  (fun total payer => total + S.capacity input payer) 0

structure C4Certificate where
  bounded : BoundedFibreState S capability input
  capacity_lt_required : totalCapacity S capability input <
    capability.required input

structure CapacityResidual where
  bounded : BoundedFibreState S capability input
  required_le_capacity : capability.required input ≤
    totalCapacity S capability input

end StructuralExhaustion.CT4
