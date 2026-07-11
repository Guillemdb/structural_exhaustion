import StructuralExhaustion.CT6.Automation
import StructuralExhaustion.Examples.CT6CT10Fixtures

namespace StructuralExhaustion.Examples.CT6Toy

open StructuralExhaustion

def mkFramework (entry : CT6.Interface.Framework) : CT6.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct4 := CT4Toy.framework
  ct7 := CT6CT10Fixtures.ct7Entry
  ct9 := CT6CT10Fixtures.ct9Entry
  ct10 := CT6CT10Fixtures.ct10Entry
  DefinitionCertified := fun _ => True
  ActiveRegime := fun _ => True
  DormantRegime := fun _ => True
  FirstFailureStructural := fun _ _ => True
  CT3Aligned := fun _ _ => True
  CT4Aligned := fun _ _ => True
  CT7Aligned := fun _ _ => True
  CT9Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct6Entry
def input : CT6.Input framework := CT6CT10Fixtures.ct6Input

private def definition (scope : CT6.ScopedState framework input) :
    CT6.DefinitionState framework input where
  scope := scope
  certificate := ⟨trivial⟩

private def active (state : CT6.DefinitionState framework input) :
    CT6.ActiveState framework input state := ⟨trivial⟩

private def dormant (state : CT6.DefinitionState framework input) :
    CT6.DormantState framework input state where
  dormant := trivial
  witness := ()
  structural := trivial

private def activePayload {state : CT6.DefinitionState framework input}
    (hot : CT6.ActiveState framework input state) :
    CT6.CT4Payload framework input hot where
  downstream := CT4Toy.input
  aligned := trivial

private def makePlan
    (activity : ∀ state : CT6.DefinitionState framework input,
      CT6.Nodes.Activity.Contract framework input state)
    (route : ∀ {state : CT6.DefinitionState framework input}
      (_cold : CT6.DormantState framework input state),
      CT6.Nodes.Dormant.Contract framework input _cold) :
    CT6.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  definition := { certify := definition }
  activity := { decide := activity }
  activeLedger := { build := activePayload }
  dormant := { classify := route }

def ct4Plan : CT6.CorePlan framework input :=
  makePlan (fun state => .active (active state))
    (fun _cold => .close { closes := trivial })

def c1Plan : CT6.CorePlan framework input :=
  makePlan (fun state => .dormant (dormant state))
    (fun _ => .close { closes := trivial })

def ct3Plan : CT6.CorePlan framework input :=
  makePlan (fun state => .dormant (dormant state))
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })

def ct7Plan : CT6.CorePlan framework input :=
  makePlan (fun state => .dormant (dormant state))
    (fun _ => .toCT7 { downstream := CT6CT10Fixtures.ct7Input, aligned := trivial })

def ct9Plan : CT6.CorePlan framework input :=
  makePlan (fun state => .dormant (dormant state))
    (fun _ => .toCT9 { downstream := CT6CT10Fixtures.ct9Input, aligned := trivial })

def ct10Plan : CT6.CorePlan framework input :=
  makePlan (fun state => .dormant (dormant state))
    (fun _ => .toCT10 { downstream := CT6CT10Fixtures.ct10Input, aligned := trivial })

def port : CT6.Port framework input where accepts := fun _ => True
def handoff : CT6.HandoffPlan framework input port where accept := fun _ => trivial

def ct4Result := CT6.runTraced framework input ct4Plan port handoff
def c1Result := CT6.runTraced framework input c1Plan port handoff
def ct3Result := CT6.runTraced framework input ct3Plan port handoff
def ct7Result := CT6.runTraced framework input ct7Plan port handoff
def ct9Result := CT6.runTraced framework input ct9Plan port handoff
def ct10Result := CT6.runTraced framework input ct10Plan port handoff

theorem ct4_terminal : ct4Result.terminal = .ct4 := rfl
theorem c1_terminal : c1Result.terminal = .c1 := rfl
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct9_terminal : ct9Result.terminal = .ct9 := rfl
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl

theorem ct4_trace : ct4Result.trace =
    [.entry, .scopeDecision, .definitionCertification, .activityDecision,
      .activeLedgerCertification, .ct4Terminal] := rfl
theorem c1_trace : c1Result.trace =
    [.entry, .scopeDecision, .definitionCertification, .activityDecision,
      .dormantDecision, .c1Terminal] := rfl
theorem ct3_trace : ct3Result.trace =
    [.entry, .scopeDecision, .definitionCertification, .activityDecision,
      .dormantDecision, .ct3Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .definitionCertification, .activityDecision,
      .dormantDecision, .ct7Terminal] := rfl
theorem ct9_trace : ct9Result.trace =
    [.entry, .scopeDecision, .definitionCertification, .activityDecision,
      .dormantDecision, .ct9Terminal] := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .definitionCertification, .activityDecision,
      .dormantDecision, .ct10Terminal] := rfl

def scopeEntry : CT6.Interface.Framework :=
  { CT6CT10Fixtures.ct6Entry with ScopeReady := fun _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT6.Input scopeFramework where
  G := (); branch := (); monitor := (); threshold := (); failureOrder := ()
def scopePlan : CT6.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  definition := { certify := fun state => False.elim state.ready }
  activity := { decide := fun state => False.elim state.scope.ready }
  activeLedger := { build := fun {definition} _ => False.elim definition.scope.ready }
  dormant := { classify := fun {definition} _ => False.elim definition.scope.ready }
def scopePort : CT6.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT6.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT6.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT6.OutcomeClaim c1Result.outcome := by
  ct6 input using c1Plan with port via handoff
example : ∃ result : CT6.ExecutionResult framework input port,
    CT6.OutcomeClaim result.outcome ∧ @CT6.Graph.ValidTrace framework input result.trace := by
  ct6_total input using c1Plan with port via handoff

end StructuralExhaustion.Examples.CT6Toy
