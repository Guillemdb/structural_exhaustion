import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.Examples.CT6CT10Fixtures

namespace StructuralExhaustion.Examples.CT9Toy

open StructuralExhaustion

def mkFramework (entry : CT9.Interface.Framework) : CT9.Framework where
  entry := entry
  ct4 := CT4Toy.framework
  ct7 := CT6CT10Fixtures.ct7Entry
  ct8 := CT6CT10Fixtures.ct8Entry
  ct10 := CT6CT10Fixtures.ct10Entry
  FibreCertified := fun _ => True
  LabelsTooCoarse := fun _ => True
  BoundedMultiplicity := fun _ => True
  Overloaded := fun _ => True
  HomogeneousExtraction := fun _ => True
  CT4Aligned := fun _ _ => True
  CT7Aligned := fun _ _ => True
  CT8Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct9Entry
def input : CT9.Input framework := CT6CT10Fixtures.ct9Input

private def fibre (scope : CT9.ScopedState framework input) :
    CT9.FibreState framework input where
  scope := scope
  certificate := ⟨trivial⟩
private def overloaded (state : CT9.FibreState framework input) :
    CT9.OverloadedState framework input state := ⟨trivial⟩
private def extraction {state : CT9.FibreState framework input}
    (over : CT9.OverloadedState framework input state) :
    CT9.ExtractionState framework input over where
  certificate := ⟨trivial⟩

private def makePlan
    (scope : CT9.Nodes.Scope.Contract framework input)
    (overload : ∀ state : CT9.FibreState framework input,
      CT9.Nodes.Overload.Contract framework input state)
    (routing : ∀ {state : CT9.FibreState framework input}
      {over : CT9.OverloadedState framework input state}
      (extract : CT9.ExtractionState framework input over),
      CT9.Nodes.Routing.Contract framework input extract) :
    CT9.CorePlan framework input where
  scope := { decide := scope }
  fibre := { certify := fibre }
  overload := { decide := overload }
  extraction := { certify := extraction }
  routing := { route := routing }

def ct10Plan : CT9.CorePlan framework input :=
  makePlan (.refine {
      coarse := trivial
      downstream := CT6CT10Fixtures.ct10Input
      aligned := trivial })
    (fun _state => .bounded {
      bounded := trivial, downstream := CT4Toy.input, aligned := trivial })
    (fun _ => .close { closes := trivial })
def ct4Plan : CT9.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun _ => .bounded {
      bounded := trivial, downstream := CT4Toy.input, aligned := trivial })
    (fun _ => .close { closes := trivial })
def c1Plan : CT9.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun state => .overloaded (overloaded state))
    (fun _ => .close { closes := trivial })
def ct7Plan : CT9.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun state => .overloaded (overloaded state))
    (fun _ => .toCT7 {
      downstream := CT6CT10Fixtures.ct7Input, aligned := trivial })
def ct8Plan : CT9.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun state => .overloaded (overloaded state))
    (fun _ => .toCT8 {
      downstream := CT6CT10Fixtures.ct8Input, aligned := trivial })

def port : CT9.Port framework input where accepts := fun _ => True
def handoff : CT9.HandoffPlan framework input port where accept := fun _ => trivial
def ct10Result := CT9.runTraced framework input ct10Plan port handoff
def ct4Result := CT9.runTraced framework input ct4Plan port handoff
def c1Result := CT9.runTraced framework input c1Plan port handoff
def ct7Result := CT9.runTraced framework input ct7Plan port handoff
def ct8Result := CT9.runTraced framework input ct8Plan port handoff
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem ct4_terminal : ct4Result.terminal = .ct4 := rfl
theorem c1_terminal : c1Result.terminal = .c1 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct8_terminal : ct8Result.terminal = .ct8 := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .ct10Terminal] := rfl
theorem ct4_trace : ct4Result.trace =
    [.entry, .scopeDecision, .fibreCertification, .overloadDecision,
      .ct4Terminal] := rfl
theorem c1_trace : c1Result.trace =
    [.entry, .scopeDecision, .fibreCertification, .overloadDecision,
      .extractionCertification, .routingDecision, .c1Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .fibreCertification, .overloadDecision,
      .extractionCertification, .routingDecision, .ct7Terminal] := rfl
theorem ct8_trace : ct8Result.trace =
    [.entry, .scopeDecision, .fibreCertification, .overloadDecision,
      .extractionCertification, .routingDecision, .ct8Terminal] := rfl

def scopeEntry : CT9.Interface.Framework :=
  { CT6CT10Fixtures.ct9Entry with ScopeReady := fun _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT9.Input scopeFramework where
  G := (); branch := (); payer := (); fibre := (); labels := (); capacity := ()
def scopePlan : CT9.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  fibre := { certify := fun state => False.elim state.ready }
  overload := { decide := fun state => False.elim state.scope.ready }
  extraction := { certify := fun {fibre} _ => False.elim fibre.scope.ready }
  routing := { route := fun {fibre} _ => False.elim fibre.scope.ready }
def scopePort : CT9.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT9.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT9.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT9.OutcomeClaim c1Result.outcome := by
  ct9 input using c1Plan with port via handoff
example : ∃ result : CT9.ExecutionResult framework input port,
    CT9.OutcomeClaim result.outcome ∧ @CT9.Graph.ValidTrace framework input result.trace := by
  ct9_total input using c1Plan with port via handoff

end StructuralExhaustion.Examples.CT9Toy
