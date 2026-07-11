import StructuralExhaustion.CT4.Automation
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT4Toy

open StructuralExhaustion

def framework : CT4.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  Demand := fun _ _ => Unit
  Payer := fun _ _ => Unit
  CapacityData := fun _ _ => Unit
  LowerBoundData := fun _ _ => Unit
  ScopeReady := fun _ _ => True
  Eligible := fun _ _ => True
  CanonicalAssignment := fun _ => True
  FibreBounded := fun _ _ => True
  DemandExceedsCapacity := fun _ _ _ => True
  C4Claim := fun _ _ => True
  ct9 := CT6CT10Fixtures.ct9Entry
  ct14 := CT6CT10Fixtures.ct14Entry
  ct13 := CT6CT10Fixtures.ct13Entry
  CT9Aligned := fun _ _ _ => True
  CT14Aligned := fun _ _ _ => True
  CT13Aligned := fun _ _ _ => True

def input : CT4.Input framework where
  G := ()
  branch := ()
  assign := fun _ => some ()
  capacity := ()
  lowerBound := ()

private def assignment
    (scope : CT4.ScopedState framework input) :
    CT4.AssignmentState framework input where
  scope := scope
  certificate := ⟨trivial⟩

private def total
    (state : CT4.AssignmentState framework input) :
    CT4.TotalAssignmentState framework input state where
  total := fun _ => ⟨(), rfl, trivial⟩

def port : CT4.Port framework input where
  accepts := fun _ => True

def handoff : CT4.HandoffPlan framework input port where
  accept := fun _ => trivial

private def basePlan
    (fibres : ∀ {assignment : CT4.AssignmentState framework input}
      (total : CT4.TotalAssignmentState framework input assignment),
      CT4.Nodes.Fibres.Contract framework input total)
    (comparison : ∀ {assignment : CT4.AssignmentState framework input}
      {total : CT4.TotalAssignmentState framework input assignment}
      (bounded : CT4.BoundedFibreState framework input total),
      CT4.Nodes.Comparison.Contract framework input bounded) :
    CT4.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  assignment := { certify := assignment }
  availability := { decide := fun state => .total (total state) }
  fibres := { decide := fibres }
  comparison := { decide := comparison }

def ct9Plan : CT4.CorePlan framework input :=
  basePlan
    (fun _ => .overloaded {
      downstream := CT6CT10Fixtures.ct9Input
      aligned := trivial
    })
    (fun _ => .close { exceeds := trivial, closes := trivial })

def c4Plan : CT4.CorePlan framework input :=
  basePlan
    (fun _ => .bounded { bounded := trivial })
    (fun _ => .close { exceeds := trivial, closes := trivial })

def ct14Plan : CT4.CorePlan framework input :=
  basePlan
    (fun _ => .bounded { bounded := trivial })
    (fun _ => .residual {
      downstream := CT6CT10Fixtures.ct14Input
      aligned := trivial
    })

def ct9Result := CT4.runTraced framework input ct9Plan port handoff
def c4Result := CT4.runTraced framework input c4Plan port handoff
def ct14Result := CT4.runTraced framework input ct14Plan port handoff

theorem ct9_terminal : ct9Result.terminal = .ct9 := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem ct14_terminal : ct14Result.terminal = .ct14 := rfl

theorem ct9_trace : ct9Result.trace =
    [.entry, .scopeDecision, .assignmentCertification,
      .availabilityDecision, .fibreDecision, .ct9Terminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .scopeDecision, .assignmentCertification,
      .availabilityDecision, .fibreDecision, .comparisonDecision,
      .c4Terminal] := rfl
theorem ct14_trace : ct14Result.trace =
    [.entry, .scopeDecision, .assignmentCertification,
      .availabilityDecision, .fibreDecision, .comparisonDecision,
      .ct14Terminal] := rfl

/-! Missing-payer recovery terminal. -/

def missingFramework : CT4.Framework :=
  { framework with Eligible := fun _ _ => False }

def missingInput : CT4.Input missingFramework where
  G := ()
  branch := ()
  assign := fun _ => none
  capacity := ()
  lowerBound := ()

private theorem totalImpossible
    {state : CT4.AssignmentState missingFramework missingInput}
    (totalState : CT4.TotalAssignmentState missingFramework missingInput state) :
    False := by
  obtain ⟨payer, assigned, _⟩ := totalState.total ()
  cases assigned

def missingPlan : CT4.CorePlan missingFramework missingInput where
  scope := { decide := .ready ⟨trivial⟩ }
  assignment := {
    certify := fun scope => { scope := scope, certificate := ⟨trivial⟩ }
  }
  availability := {
    decide := fun _ => .missing {
      witness := {
        demand := ()
        unassigned := rfl
        unavailable := fun _ eligible => eligible
      }
      downstream := CT6CT10Fixtures.ct13Input
      aligned := trivial
    }
  }
  fibres := { decide := fun totalState => False.elim (totalImpossible totalState) }
  comparison := {
    decide := fun {_} {totalState} _ =>
      False.elim (totalImpossible totalState)
  }

def missingPort : CT4.Port missingFramework missingInput where
  accepts := fun _ => True

def missingHandoff :
    CT4.HandoffPlan missingFramework missingInput missingPort where
  accept := fun _ => trivial

def ct13Result :=
  CT4.runTraced missingFramework missingInput missingPlan
    missingPort missingHandoff

theorem ct13_terminal : ct13Result.terminal = .ct13 := rfl
theorem ct13_trace : ct13Result.trace =
    [.entry, .scopeDecision, .assignmentCertification,
      .availabilityDecision, .ct13Terminal] := rfl

/-! Typed scope terminal. -/

def scopeFramework : CT4.Framework :=
  { framework with ScopeReady := fun _ _ => False }

def scopeInput : CT4.Input scopeFramework where
  G := ()
  branch := ()
  assign := fun _ => some ()
  capacity := ()
  lowerBound := ()

def scopePlan : CT4.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  assignment := { certify := fun state => False.elim state.ready }
  availability := {
    decide := fun state => False.elim state.scope.ready
  }
  fibres := {
    decide := fun {state} _ => False.elim state.scope.ready
  }
  comparison := {
    decide := fun {state} {_} _ => False.elim state.scope.ready
  }

def scopePort : CT4.Port scopeFramework scopeInput where
  accepts := fun _ => True

def scopeHandoff : CT4.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial

def scopeResult :=
  CT4.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff

theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace :
    scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT4.OutcomeClaim c4Result.outcome := by
  ct4 input using c4Plan with port via handoff

example : ∃ result : CT4.ExecutionResult framework input port,
    CT4.OutcomeClaim result.outcome ∧
      @CT4.Graph.ValidTrace framework input result.trace := by
  ct4_total input using c4Plan with port via handoff

end StructuralExhaustion.Examples.CT4Toy
