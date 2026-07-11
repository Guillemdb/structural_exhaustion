import StructuralExhaustion.CT7.Automation
import StructuralExhaustion.Examples.CT6CT10Fixtures

namespace StructuralExhaustion.Examples.CT7Toy

open StructuralExhaustion

def mkFramework (entry : CT7.Interface.Framework) : CT7.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct10 := CT6CT10Fixtures.ct10Entry
  ct12 := CT6CT10Fixtures.ct12Entry
  ct16 := CT6CT10Fixtures.ct16Entry
  ContextComplete := fun _ => True
  NoRealization := fun _ => True
  Distinguishing := fun _ => True
  NeutralResponses := fun _ => True
  CT3Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True
  CT12Aligned := fun _ _ => True
  CT16Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct7Entry
def input : CT7.Input framework := CT6CT10Fixtures.ct7Input

private def context (scope : CT7.ScopedState framework input) :
    CT7.ContextState framework input where
  scope := scope
  certificate := ⟨trivial⟩
private def unrealized (state : CT7.ContextState framework input) :
    CT7.UnrealizedState framework input state := ⟨trivial⟩
private def defect {state : CT7.ContextState framework input}
    (none : CT7.UnrealizedState framework input state) :
    CT7.DefectState framework input none := ⟨trivial⟩
private def neutral {state : CT7.ContextState framework input}
    (none : CT7.UnrealizedState framework input state) :
    CT7.NeutralState framework input none := ⟨trivial⟩

private def makePlan
    (realization : ∀ state : CT7.ContextState framework input,
      CT7.Nodes.Realization.Contract framework input state)
    (distinction : ∀ {state : CT7.ContextState framework input}
      (none : CT7.UnrealizedState framework input state),
      CT7.Nodes.Distinction.Contract framework input none)
    (defectRoute : ∀ {state : CT7.ContextState framework input}
      {none : CT7.UnrealizedState framework input state}
      (found : CT7.DefectState framework input none),
      CT7.Nodes.Defect.Contract framework input found)
    (neutralRoute : ∀ {state : CT7.ContextState framework input}
      {none : CT7.UnrealizedState framework input state}
      (same : CT7.NeutralState framework input none),
      CT7.Nodes.Neutral.Contract framework input same) :
    CT7.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  context := { certify := context }
  realization := { decide := realization }
  distinction := { decide := distinction }
  defect := { classify := defectRoute }
  neutral := { classify := neutralRoute }

private def defectChoice {state : CT7.ContextState framework input}
    (none : CT7.UnrealizedState framework input state) :=
  CT7.Nodes.Distinction.Decision.defect (defect none)
private def neutralChoice {state : CT7.ContextState framework input}
    (none : CT7.UnrealizedState framework input state) :=
  CT7.Nodes.Distinction.Decision.neutral (neutral none)

def c1Plan : CT7.CorePlan framework input :=
  makePlan (fun _state => .close { closes := trivial }) defectChoice
    (fun _found => .close { closes := trivial })
    (fun _same => .close { closes := trivial })
def c3Plan : CT7.CorePlan framework input :=
  makePlan (fun state => .unrealized (unrealized state)) defectChoice
    (fun _ => .close { closes := trivial })
    (fun _ => .close { closes := trivial })
def ct3Plan : CT7.CorePlan framework input :=
  makePlan (fun state => .unrealized (unrealized state)) defectChoice
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
    (fun _ => .close { closes := trivial })
def ct12Plan : CT7.CorePlan framework input :=
  makePlan (fun state => .unrealized (unrealized state)) defectChoice
    (fun _ => .toCT12 {
      downstream := CT6CT10Fixtures.ct12Input, aligned := trivial })
    (fun _ => .close { closes := trivial })
def c2Plan : CT7.CorePlan framework input :=
  makePlan (fun state => .unrealized (unrealized state)) neutralChoice
    (fun _ => .close { closes := trivial })
    (fun _ => .close { closes := trivial })
def ct10Plan : CT7.CorePlan framework input :=
  makePlan (fun state => .unrealized (unrealized state)) neutralChoice
    (fun _ => .close { closes := trivial })
    (fun _ => .toCT10 {
      downstream := CT6CT10Fixtures.ct10Input, aligned := trivial })
def ct16Plan : CT7.CorePlan framework input :=
  makePlan (fun state => .unrealized (unrealized state)) neutralChoice
    (fun _ => .close { closes := trivial })
    (fun _ => .toCT16 {
      downstream := CT6CT10Fixtures.ct16Input, aligned := trivial })

def port : CT7.Port framework input where accepts := fun _ => True
def handoff : CT7.HandoffPlan framework input port where accept := fun _ => trivial

def c1Result := CT7.runTraced framework input c1Plan port handoff
def c3Result := CT7.runTraced framework input c3Plan port handoff
def ct3Result := CT7.runTraced framework input ct3Plan port handoff
def ct12Result := CT7.runTraced framework input ct12Plan port handoff
def c2Result := CT7.runTraced framework input c2Plan port handoff
def ct10Result := CT7.runTraced framework input ct10Plan port handoff
def ct16Result := CT7.runTraced framework input ct16Plan port handoff

theorem c1_terminal : c1Result.terminal = .c1 := rfl
theorem c3_terminal : c3Result.terminal = .c3 := rfl
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem ct12_terminal : ct12Result.terminal = .ct12 := rfl
theorem c2_terminal : c2Result.terminal = .c2 := rfl
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem ct16_terminal : ct16Result.terminal = .ct16 := rfl

theorem c1_trace : c1Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .c1Terminal] := rfl
theorem c3_trace : c3Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .distinctionDecision, .defectDecision, .c3Terminal] := rfl
theorem ct3_trace : ct3Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .distinctionDecision, .defectDecision, .ct3Terminal] := rfl
theorem ct12_trace : ct12Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .distinctionDecision, .defectDecision, .ct12Terminal] := rfl
theorem c2_trace : c2Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .distinctionDecision, .neutralDecision, .c2Terminal] := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .distinctionDecision, .neutralDecision, .ct10Terminal] := rfl
theorem ct16_trace : ct16Result.trace =
    [.entry, .scopeDecision, .contextCertification, .realizationDecision,
      .distinctionDecision, .neutralDecision, .ct16Terminal] := rfl

def scopeEntry : CT7.Interface.Framework :=
  { CT6CT10Fixtures.ct7Entry with ScopeReady := fun _ _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT7.Input scopeFramework where
  G := (); branch := (); left := (); right := (); boundary := (); exchange := (); contexts := ()
def scopePlan : CT7.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  context := { certify := fun state => False.elim state.ready }
  realization := { decide := fun state => False.elim state.scope.ready }
  distinction := { decide := fun {context} _ => False.elim context.scope.ready }
  defect := { classify := fun {context} _ => False.elim context.scope.ready }
  neutral := { classify := fun {context} _ => False.elim context.scope.ready }
def scopePort : CT7.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT7.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT7.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT7.OutcomeClaim c2Result.outcome := by
  ct7 input using c2Plan with port via handoff
example : ∃ result : CT7.ExecutionResult framework input port,
    CT7.OutcomeClaim result.outcome ∧ @CT7.Graph.ValidTrace framework input result.trace := by
  ct7_total input using c2Plan with port via handoff

end StructuralExhaustion.Examples.CT7Toy
