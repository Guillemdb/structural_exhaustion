import Hypostructure.CT4.Capability
import Hypostructure.Core.Finite.Accounting

/-!
# CT4 generated charging states

Every assignment and fibre is computed from the two exact schedules queried
from the predecessor.  Generated state constructors are private; callers can
inspect certificates but cannot manufacture an assignment or bounded-fibre
state.
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDemand, uPayer} Previous}

/-- Canonical first-eligible search for one demand. -/
def assignmentExecution (capability : Capability spec) (previous : Previous)
    (demand : spec.Demand previous) :
    Core.Finite.Search.Execution (capability.payersAt previous)
      (spec.Eligible previous demand) :=
  Core.Finite.Search.run (capability.payersAt previous)
    (spec.Eligible previous demand)
    (capability.eligibleDecidable previous demand)

/-- Framework-computed assignment table. -/
structure AssignmentState (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  execution : (demand : spec.Demand previous) ->
    Core.Finite.Search.Execution (capability.payersAt previous)
      (spec.Eligible previous demand)
  exact : forall demand,
    execution demand = assignmentExecution capability previous demand

/-- Build the unique canonical first-eligible assignment table. -/
def computeAssignment (capability : Capability spec) (previous : Previous) :
    AssignmentState capability previous :=
  .mk (assignmentExecution capability previous) (fun _demand => rfl)

namespace AssignmentState

/-- Observable canonical assigned payer, if the payer scan succeeds. -/
def assignedPayer? {capability : Capability spec} {previous : Previous}
    (assignment : AssignmentState capability previous)
    (demand : spec.Demand previous) : Option (spec.Payer previous) :=
  (assignment.execution demand).value?

/-- Exact assignment-search work over every inherited demand. -/
def checks {capability : Capability spec} {previous : Previous}
    (assignment : AssignmentState capability previous) : Nat :=
  ((capability.demandsAt previous).values.map fun demand =>
    Core.Finite.Accounting.executionChecks
      (assignment.execution demand)).sum

/-- Every exact assignment-table computation is bounded by the product of
the two inherited schedule cardinalities. -/
theorem checks_le_product {capability : Capability spec}
    {previous : Previous}
    (assignment : AssignmentState capability previous) :
    assignment.checks <=
      (capability.demandsAt previous).card *
        (capability.payersAt previous).card := by
  unfold checks
  calc
    ((capability.demandsAt previous).values.map fun demand =>
        Core.Finite.Accounting.executionChecks
          (assignment.execution demand)).sum <=
        ((capability.demandsAt previous).values.map fun _demand =>
          (capability.payersAt previous).card).sum := by
      apply List.sum_le_sum
      intro demand _member
      exact Core.Finite.Accounting.executionChecks_le_card
        (assignment.execution demand)
    _ = (capability.demandsAt previous).card *
        (capability.payersAt previous).card := by
      simp [Core.Finite.Enumeration.card]

/-- A scheduled eligibility witness forces the canonical assignment search to
take its hit branch. -/
theorem hasHit_of_eligible {capability : Capability spec}
    {previous : Previous}
    (assignment : AssignmentState capability previous)
    (demand : spec.Demand previous) (payer : spec.Payer previous)
    (payerMember : payer ∈ (capability.payersAt previous).values)
    (eligible : spec.Eligible previous demand payer) :
    (assignment.execution demand).HasHit := by
  rw [assignment.exact demand]
  exact Core.Finite.Search.complete (capability.payersAt previous)
    (spec.Eligible previous demand)
    (capability.eligibleDecidable previous demand)
    ⟨payer, payerMember, eligible⟩

/-- Any selected payer is eligible for its demand. -/
theorem assignedPayer_sound {capability : Capability spec}
    {previous : Previous}
    (assignment : AssignmentState capability previous)
    (demand : spec.Demand previous) (payer : spec.Payer previous)
    (assigned : assignment.assignedPayer? demand = some payer) :
    spec.Eligible previous demand payer := by
  unfold assignedPayer? at assigned
  rw [assignment.exact demand] at assigned
  exact (Core.Finite.Search.value_sound (capability.payersAt previous)
    (spec.Eligible previous demand)
    (capability.eligibleDecidable previous demand) assigned).2

end AssignmentState

/-- The canonical assignment has no hit for this scheduled demand. -/
def MissingAssignment (capability : Capability spec) (previous : Previous)
    (assignment : AssignmentState capability previous)
    (demand : spec.Demand previous) : Prop :=
  Not (assignment.execution demand).HasHit

/-- First demand with no eligible payer in the exact inherited payer
schedule. -/
abbrev MissingPayerResidual (capability : Capability spec)
    (previous : Previous) (assignment : AssignmentState capability previous) :=
  Core.Finite.Search.IndexedHit (capability.demandsAt previous)
    (MissingAssignment capability previous assignment)

namespace MissingPayerResidual

/-- Canonically selected missing demand. -/
def demand {capability : Capability spec} {previous : Previous}
    {assignment : AssignmentState capability previous}
    (residual : MissingPayerResidual capability previous assignment) :
    spec.Demand previous :=
  residual.value

/-- The selected demand belongs to the literal incoming schedule. -/
theorem scheduled {capability : Capability spec} {previous : Previous}
    {assignment : AssignmentState capability previous}
    (residual : MissingPayerResidual capability previous assignment) :
    residual.demand ∈ (capability.demandsAt previous).values :=
  residual.member

/-- No payer in the inherited payer schedule is eligible for the selected
demand.  No assertion is made about an ambient payer outside that schedule. -/
theorem noEligible {capability : Capability spec} {previous : Previous}
    {assignment : AssignmentState capability previous}
    (residual : MissingPayerResidual capability previous assignment) :
    forall payer,
      payer ∈ (capability.payersAt previous).values ->
        Not (spec.Eligible previous residual.demand payer) := by
  intro payer payerMember eligible
  exact residual.sound
    (assignment.hasHit_of_eligible residual.demand payer payerMember eligible)

end MissingPayerResidual

/-- Exhaustive availability of a canonical payer for every inherited demand. -/
structure TotalAssignmentState (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  assignment : AssignmentState capability previous
  total : forall demand,
    demand ∈ (capability.demandsAt previous).values ->
      (assignment.execution demand).HasHit

/-- Build totality from exhaustive failure of the missing-demand predicate. -/
def totalAssignmentOfAvoids {capability : Capability spec}
    {previous : Previous} (assignment : AssignmentState capability previous)
    (avoids : Core.Finite.Search.Avoids (capability.demandsAt previous)
      (MissingAssignment capability previous assignment)) :
    TotalAssignmentState capability previous :=
  .mk assignment (by
    intro demand member
    obtain ⟨index, indexed⟩ :=
      ((capability.demandsAt previous).mem_iff_exists_index demand).mp member
    by_contra missing
    have noMissing := avoids index
    rw [indexed] at noMissing
    exact noMissing missing)

/-- Canonical demand fibre over one payer. -/
def fibre {capability : Capability spec} {previous : Previous}
    (assignment : AssignmentState capability previous)
    (payer : spec.Payer previous) : List (spec.Demand previous) := by
  letI : DecidableEq (spec.Payer previous) :=
    (capability.payersAt previous).decEq
  exact (capability.demandsAt previous).values.filter fun demand =>
    assignment.assignedPayer? demand = some payer

/-- Exact total weight assigned to one payer. -/
def fibreWeight {capability : Capability spec} {previous : Previous}
    (assignment : AssignmentState capability previous)
    (payer : spec.Payer previous) : Nat :=
  (fibre assignment payer).map (spec.demandWeight previous) |>.sum

/-- A payer receives more assigned weight than its declared capacity. -/
def Overloaded (capability : Capability spec) (previous : Previous)
    (total : TotalAssignmentState capability previous)
    (payer : spec.Payer previous) : Prop :=
  spec.capacity previous payer < fibreWeight total.assignment payer

/-- First overloaded payer in the exact inherited payer schedule. -/
abbrev OverloadedFibreResidual (capability : Capability spec)
    (previous : Previous) (total : TotalAssignmentState capability previous) :=
  Core.Finite.Search.IndexedHit (capability.payersAt previous)
    (Overloaded capability previous total)

/-- Exhaustive absence of overload on the exact inherited payer schedule. -/
abbrev BoundedFibreState (capability : Capability spec)
    (previous : Previous) (total : TotalAssignmentState capability previous) :=
  Core.Finite.Search.Avoids (capability.payersAt previous)
    (Overloaded capability previous total)

/-- Total capacity of the exact inherited payer schedule. -/
def totalCapacity (capability : Capability spec) (previous : Previous) : Nat :=
  (capability.payersAt previous).values.map (spec.capacity previous) |>.sum

/-- Strict aggregate capacity gap, the CT4/C4 certificate terminal. -/
def C4Certificate (capability : Capability spec) (previous : Previous) : Prop :=
  totalCapacity capability previous < spec.required previous

/-- Complementary aggregate-capacity residual. -/
def CapacityResidual (capability : Capability spec) (previous : Previous) :
    Prop :=
  spec.required previous <= totalCapacity capability previous

end Hypostructure.CT4
