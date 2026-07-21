import Hypostructure.CT4.State
import Hypostructure.Core.Residual.Decision

/-!
# CT4 deterministic scans and Core routing

CT4 performs one canonical assignment pass, then routes missing-demand,
overloaded-fibre, and aggregate-capacity decisions through Core.  Every scan
uses only schedules queried from the literal predecessor.
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDemand, uPayer} Previous}

/-- Primitive decision that one canonical assignment has no payer. -/
def missingAssignmentDecidable {capability : Capability spec}
    {previous : Previous} (assignment : AssignmentState capability previous)
    (demand : spec.Demand previous) :
    Decidable (MissingAssignment capability previous assignment demand) :=
  by
    unfold MissingAssignment
    infer_instance

/-- Counted first missing-demand scan. -/
def countedAvailabilityScan (capability : Capability spec)
    (previous : Previous) (assignment : AssignmentState capability previous) :
    Core.Counted (Core.Finite.Search.Execution
      (capability.demandsAt previous)
      (MissingAssignment capability previous assignment)) :=
  Core.Finite.Accounting.countedRun (capability.demandsAt previous)
    (MissingAssignment capability previous assignment)
    (missingAssignmentDecidable assignment)

/-- Proof-carrying first missing-demand scan. -/
def availabilityScan (capability : Capability spec) (previous : Previous)
    (assignment : AssignmentState capability previous) :
    Core.Finite.Search.Execution (capability.demandsAt previous)
      (MissingAssignment capability previous assignment) :=
  (countedAvailabilityScan capability previous assignment).value

/-- Core-owned availability route. -/
abbrev RoutedAvailability (capability : Capability spec)
    (previous : Previous) (assignment : AssignmentState capability previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.demandsAt previous)
        (MissingAssignment capability previous assignment) =>
      execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.demandsAt previous)
        (MissingAssignment capability previous assignment) =>
      Core.Finite.Search.Avoids (capability.demandsAt previous)
        (MissingAssignment capability previous assignment))

/-- Route the availability scan through Core's binary decision executor. -/
def routeAvailability (capability : Capability spec) (previous : Previous)
    (assignment : AssignmentState capability previous) :
    RoutedAvailability capability previous assignment :=
  Core.Finite.Search.route
    (availabilityScan capability previous assignment)

/-- Primitive overload comparison for one payer. -/
def overloadedDecidable {capability : Capability spec}
    {previous : Previous} (total : TotalAssignmentState capability previous)
    (payer : spec.Payer previous) :
    Decidable (Overloaded capability previous total payer) :=
  Nat.decLt _ _

/-- Counted first overloaded-fibre scan.  Its Core count records payer
comparisons; `Execution.outcomeChecks` additionally charges the complete
demand-fibre scan performed by each comparison. -/
def countedOverloadScan (capability : Capability spec) (previous : Previous)
    (total : TotalAssignmentState capability previous) :
    Core.Counted (Core.Finite.Search.Execution (capability.payersAt previous)
      (Overloaded capability previous total)) :=
  Core.Finite.Accounting.countedRun (capability.payersAt previous)
    (Overloaded capability previous total) (overloadedDecidable total)

/-- Proof-carrying first overloaded-fibre scan. -/
def overloadScan (capability : Capability spec) (previous : Previous)
    (total : TotalAssignmentState capability previous) :
    Core.Finite.Search.Execution (capability.payersAt previous)
      (Overloaded capability previous total) :=
  (countedOverloadScan capability previous total).value

/-- Core-owned overload route. -/
abbrev RoutedOverload (capability : Capability spec) (previous : Previous)
    (total : TotalAssignmentState capability previous) :=
  Core.Residual.Decision.Stage
    (fun execution : Core.Finite.Search.Execution
        (capability.payersAt previous)
        (Overloaded capability previous total) => execution.HasHit)
    (fun _execution : Core.Finite.Search.Execution
        (capability.payersAt previous)
        (Overloaded capability previous total) =>
      BoundedFibreState capability previous total)

/-- Route the overload scan through Core's search decision. -/
def routeOverload (capability : Capability spec) (previous : Previous)
    (total : TotalAssignmentState capability previous) :
    RoutedOverload capability previous total :=
  Core.Finite.Search.route (overloadScan capability previous total)

/-- Every scheduled payer is within capacity on the exhaustive no-overload
branch. -/
theorem BoundedFibreState.boundedAt {capability : Capability spec}
    {previous : Previous} {total : TotalAssignmentState capability previous}
    (bounded : BoundedFibreState capability previous total)
    (payer : spec.Payer previous)
    (member : payer ∈ (capability.payersAt previous).values) :
    fibreWeight total.assignment payer <= spec.capacity previous payer := by
  obtain ⟨index, indexed⟩ :=
    ((capability.payersAt previous).mem_iff_exists_index payer).mp member
  have notOverloaded := bounded index
  rw [indexed] at notOverloaded
  exact Nat.le_of_not_gt notOverloaded

/-- Core comparison node for strict C4 gap versus capacity residual. -/
def capacityNode (capability : Capability spec) :
    Core.Residual.Decision.Node Previous
      (fun current => C4Certificate capability current)
      (fun current => CapacityResidual capability current) :=
  Core.Residual.Decision.Node.create
    (fun current => Nat.decLt
      (totalCapacity capability current) (spec.required current))
    (by
      intro current notStrict
      exact Nat.le_of_not_gt notStrict)

/-- Core-owned final aggregate-capacity route. -/
abbrev RoutedCapacity (capability : Capability spec) :=
  Core.Residual.Decision.Stage
    (fun previous => C4Certificate capability previous)
    (fun previous => CapacityResidual capability previous)

/-- Compare required mass with total scheduled capacity through Core. -/
def compareCapacity (capability : Capability spec) (previous : Previous) :
    RoutedCapacity capability :=
  (capacityNode capability).run previous

end Hypostructure.CT4
