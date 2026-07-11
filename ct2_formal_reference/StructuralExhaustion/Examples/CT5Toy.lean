import StructuralExhaustion.CT5.Automation
import StructuralExhaustion.Examples.CT4Toy

namespace StructuralExhaustion.Examples.CT5Toy

open StructuralExhaustion

def framework : CT5.Framework where
  ct4 := CT4Toy.framework
  ct11 := CT6CT10Fixtures.ct11Entry
  ct14 := CT6CT10Fixtures.ct14Entry
  Site := fun _ _ => Unit
  LocalWitness := fun _ _ _ => Unit
  ScopeReady := fun _ _ => True
  Active := fun _ => True
  WitnessSupports := fun _ _ => True
  LocalityHolds := fun _ => True
  LocalLedgerReady := fun _ => True
  SummationHolds := fun _ => True
  CT11Aligned := fun _ _ _ => True
  CT14Aligned := fun _ _ _ => True

def input : CT5.Input framework where
  G := ()
  branch := ()
  extract := fun _ => some ()

private def locality
    (scope : CT5.ScopedState framework input) :
    CT5.LocalityState framework input where
  scope := scope
  certificate := ⟨trivial⟩

private def ledger
    (state : CT5.LocalityState framework input) :
    CT5.LocalLedgerState framework input state where
  ready := trivial

def port : CT5.Port framework input where
  accepts := fun _ => True

def handoff : CT5.HandoffPlan framework input port where
  accept := fun _ => trivial

private def basePlan
    (deficit : ∀ state : CT5.LocalityState framework input,
      CT5.Nodes.Deficit.Contract framework input state)
    (comparison : ∀ {locality : CT5.LocalityState framework input}
      {ledger : CT5.LocalLedgerState framework input locality}
      (summation : CT5.SummationState framework input ledger),
      CT5.Nodes.Comparison.Contract framework input summation) :
    CT5.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  locality := { certify := locality }
  deficit := { classify := deficit }
  summation := { certify := fun _ => ⟨trivial⟩ }
  comparison := { classify := comparison }

def ct11Plan : CT5.CorePlan framework input :=
  basePlan
    (fun _ => .toCT11 {
      downstream := CT6CT10Fixtures.ct11Input
      aligned := trivial
    })
    (fun _ => .close { closes := trivial })

def c4Plan : CT5.CorePlan framework input :=
  basePlan
    (fun state => .ledger (ledger state))
    (fun _ => .close { closes := trivial })

def ct4Plan : CT5.CorePlan framework input :=
  basePlan
    (fun state => .ledger (ledger state))
    (fun _ => .toCT4 {
      assign := fun _ => some ()
      capacity := ()
      lowerBound := ()
    })

def ct14Plan : CT5.CorePlan framework input :=
  basePlan
    (fun state => .ledger (ledger state))
    (fun _ => .toCT14 {
      downstream := CT6CT10Fixtures.ct14Input
      aligned := trivial
    })

def ct11Result := CT5.runTraced framework input ct11Plan port handoff
def c4Result := CT5.runTraced framework input c4Plan port handoff
def ct4Result := CT5.runTraced framework input ct4Plan port handoff
def ct14Result := CT5.runTraced framework input ct14Plan port handoff

theorem ct11_terminal : ct11Result.terminal = .ct11 := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem ct4_terminal : ct4Result.terminal = .ct4 := rfl
theorem ct14_terminal : ct14Result.terminal = .ct14 := rfl

theorem ct11_trace : ct11Result.trace =
    [.entry, .scopeDecision, .localityCertification,
      .deficitDecision, .ct11Terminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .scopeDecision, .localityCertification,
      .deficitDecision, .summationCertification, .comparisonDecision,
      .c4Terminal] := rfl
theorem ct4_trace : ct4Result.trace =
    [.entry, .scopeDecision, .localityCertification,
      .deficitDecision, .summationCertification, .comparisonDecision,
      .ct4Terminal] := rfl
theorem ct14_trace : ct14Result.trace =
    [.entry, .scopeDecision, .localityCertification,
      .deficitDecision, .summationCertification, .comparisonDecision,
      .ct14Terminal] := rfl

/-! Typed scope terminal. -/

def scopeFramework : CT5.Framework :=
  { framework with ScopeReady := fun _ _ => False }

def scopeInput : CT5.Input scopeFramework where
  G := ()
  branch := ()
  extract := fun _ => some ()

def scopePlan : CT5.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  locality := { certify := fun state => False.elim state.ready }
  deficit := {
    classify := fun state => False.elim state.scope.ready
  }
  summation := {
    certify := fun {state} _ => False.elim state.scope.ready
  }
  comparison := {
    classify := fun {state} {_} _ => False.elim state.scope.ready
  }

def scopePort : CT5.Port scopeFramework scopeInput where
  accepts := fun _ => True

def scopeHandoff : CT5.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial

def scopeResult :=
  CT5.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff

theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace :
    scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

/-! Exact CT5 to CT4 adapter and downstream execution. -/

def downstreamInput : CT4.Input CT4Toy.framework :=
  match ct4Result.outcome with
  | .ct4 payload _ => payload.toInput

private def downstreamAssignment
    (scope : CT4.ScopedState CT4Toy.framework downstreamInput) :
    CT4.AssignmentState CT4Toy.framework downstreamInput where
  scope := scope
  certificate := ⟨trivial⟩

private def downstreamTotal
    (state : CT4.AssignmentState CT4Toy.framework downstreamInput) :
    CT4.TotalAssignmentState CT4Toy.framework downstreamInput state where
  total := fun _ => ⟨(), rfl, trivial⟩

def downstreamPlan : CT4.CorePlan CT4Toy.framework downstreamInput where
  scope := { decide := .ready ⟨trivial⟩ }
  assignment := { certify := downstreamAssignment }
  availability := {
    decide := fun state => .total (downstreamTotal state)
  }
  fibres := { decide := fun _ => .bounded ⟨trivial⟩ }
  comparison := {
    decide := fun _ => .close { exceeds := trivial, closes := trivial }
  }

def downstreamPort : CT4.Port CT4Toy.framework downstreamInput where
  accepts := fun _ => True

def downstreamHandoff :
    CT4.HandoffPlan CT4Toy.framework downstreamInput downstreamPort where
  accept := fun _ => trivial

def downstreamResult :=
  CT4.runTraced CT4Toy.framework downstreamInput downstreamPlan
    downstreamPort downstreamHandoff

theorem adapter_preserves_ambient : downstreamInput.G = input.G := rfl
theorem adapter_preserves_branch : downstreamInput.branch = input.branch := rfl
theorem downstream_terminal : downstreamResult.terminal = .c4 := rfl
theorem downstream_trace : downstreamResult.trace =
    [.entry, .scopeDecision, .assignmentCertification,
      .availabilityDecision, .fibreDecision, .comparisonDecision,
      .c4Terminal] := rfl

example : CT5.OutcomeClaim ct4Result.outcome := by
  ct5 input using ct4Plan with port via handoff

example : ∃ result : CT5.ExecutionResult framework input port,
    CT5.OutcomeClaim result.outcome ∧
      @CT5.Graph.ValidTrace framework input result.trace := by
  ct5_total input using ct4Plan with port via handoff

end StructuralExhaustion.Examples.CT5Toy
