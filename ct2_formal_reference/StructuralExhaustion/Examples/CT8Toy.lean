import StructuralExhaustion.CT8.Automation
import StructuralExhaustion.Examples.CT6CT10Fixtures

namespace StructuralExhaustion.Examples.CT8Toy

open StructuralExhaustion

def mkFramework (entry : CT8.Interface.Framework) : CT8.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct7 := CT6CT10Fixtures.ct7Entry
  ct10 := CT6CT10Fixtures.ct10Entry
  TypeEqualityCertified := fun _ => True
  CoarseLabel := fun _ => True
  ShortSequence := fun _ => True
  RepeatedType := fun _ => True
  Indistinguishable := fun _ => True
  Separating := fun _ => True
  CT3Aligned := fun _ _ => True
  CT7Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct8Entry
def input : CT8.Input framework := CT6CT10Fixtures.ct8Input

private def equality (scope : CT8.ScopedState framework input) :
    CT8.EqualityState framework input where
  scope := scope
  certificate := ⟨trivial⟩
private def repeated (state : CT8.EqualityState framework input) :
    CT8.RepeatedState framework input state := ⟨trivial⟩
private def separating {state : CT8.EqualityState framework input}
    (repeatedState : CT8.RepeatedState framework input state) :
    CT8.SeparatingState framework input repeatedState := ⟨trivial⟩

private def makePlan
    (scope : CT8.Nodes.Scope.Contract framework input)
    (repetition : ∀ state : CT8.EqualityState framework input,
      CT8.Nodes.Repetition.Contract framework input state)
    (response : ∀ {state : CT8.EqualityState framework input}
      (repeatedState : CT8.RepeatedState framework input state),
      CT8.Nodes.Response.Contract framework input repeatedState)
    (routing : ∀ {state : CT8.EqualityState framework input}
      {repeatedState : CT8.RepeatedState framework input state}
      (split : CT8.SeparatingState framework input repeatedState),
      CT8.Nodes.Routing.Contract framework input split) :
    CT8.CorePlan framework input where
  scope := { decide := scope }
  equivalence := { certify := equality }
  repetition := { decide := repetition }
  response := { decide := response }
  routing := { route := routing }

def ct10Plan : CT8.CorePlan framework input :=
  makePlan (.refine {
      coarse := trivial
      downstream := CT6CT10Fixtures.ct10Input
      aligned := trivial })
    (fun _state => .short { short := trivial, closes := trivial })
    (fun _ => .close { equivalent := trivial, closes := trivial })
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
def c5Plan : CT8.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun _state => .short { short := trivial, closes := trivial })
    (fun _ => .close { equivalent := trivial, closes := trivial })
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
def c2Plan : CT8.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun state => .repeated (repeated state))
    (fun _ => .close { equivalent := trivial, closes := trivial })
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
def ct3Plan : CT8.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun state => .repeated (repeated state))
    (fun repeatedState => .separating (separating repeatedState))
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
def ct7Plan : CT8.CorePlan framework input :=
  makePlan (.ready ⟨trivial⟩)
    (fun state => .repeated (repeated state))
    (fun repeatedState => .separating (separating repeatedState))
    (fun _ => .toCT7 {
      downstream := CT6CT10Fixtures.ct7Input, aligned := trivial })

def port : CT8.Port framework input where accepts := fun _ => True
def handoff : CT8.HandoffPlan framework input port where accept := fun _ => trivial
def ct10Result := CT8.runTraced framework input ct10Plan port handoff
def c5Result := CT8.runTraced framework input c5Plan port handoff
def c2Result := CT8.runTraced framework input c2Plan port handoff
def ct3Result := CT8.runTraced framework input ct3Plan port handoff
def ct7Result := CT8.runTraced framework input ct7Plan port handoff
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem c5_terminal : c5Result.terminal = .c5 := rfl
theorem c2_terminal : c2Result.terminal = .c2 := rfl
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .ct10Terminal] := rfl
theorem c5_trace : c5Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .repetitionDecision, .c5Terminal] := rfl
theorem c2_trace : c2Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .repetitionDecision, .responseDecision, .c2Terminal] := rfl
theorem ct3_trace : ct3Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .repetitionDecision, .responseDecision, .routingDecision, .ct3Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .repetitionDecision, .responseDecision, .routingDecision, .ct7Terminal] := rfl

def scopeEntry : CT8.Interface.Framework :=
  { CT6CT10Fixtures.ct8Entry with ScopeReady := fun _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT8.Input scopeFramework where
  G := (); branch := (); sequence := (); typeSystem := (); threshold := ()
def scopePlan : CT8.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  equivalence := { certify := fun state => False.elim state.ready }
  repetition := { decide := fun state => False.elim state.scope.ready }
  response := { decide := fun {equality} _ => False.elim equality.scope.ready }
  routing := { route := fun {equality} _ => False.elim equality.scope.ready }
def scopePort : CT8.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT8.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT8.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT8.OutcomeClaim c2Result.outcome := by
  ct8 input using c2Plan with port via handoff
example : ∃ result : CT8.ExecutionResult framework input port,
    CT8.OutcomeClaim result.outcome ∧ @CT8.Graph.ValidTrace framework input result.trace := by
  ct8_total input using c2Plan with port via handoff

end StructuralExhaustion.Examples.CT8Toy
