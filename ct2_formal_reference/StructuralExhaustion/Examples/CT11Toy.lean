import StructuralExhaustion.CT11.Automation
import StructuralExhaustion.Examples.CT1Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT11Toy
open StructuralExhaustion

def mkFramework (entry : CT11.Interface.Framework) : CT11.Framework where
  entry := entry
  ct1 := CT1Toy.routingFramework
  ct7 := CT6CT10Fixtures.ct7Entry
  ct10 := CT6CT10Fixtures.ct10Entry
  ct14 := CT6CT10Fixtures.ct14Entry
  DecompositionCertified := fun _ => True
  AdmissibilityClosed := fun _ => True
  SummationCertified := fun _ => True
  LocalDeficitExists := fun _ => True
  CT1Aligned := fun _ _ => True
  CT7Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True
  CT14Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct11Entry
def input : CT11.Input framework := CT6CT10Fixtures.ct11Input
private def decomposition (scope : CT11.ScopedState framework input) :
    CT11.DecompositionState framework input := ⟨scope, trivial⟩
private def admissible (state : CT11.DecompositionState framework input) :
    CT11.AdmissibleState framework input state := ⟨trivial⟩
private def localized {state : CT11.DecompositionState framework input}
    (closed : CT11.AdmissibleState framework input state) :
    CT11.LocalizationState framework input closed := ⟨trivial, trivial⟩

private def makePlan
    (admission : ∀ state : CT11.DecompositionState framework input,
      CT11.Nodes.Admissibility.Contract framework input state)
    (route : ∀ {state : CT11.DecompositionState framework input}
      {closed : CT11.AdmissibleState framework input state}
      (found : CT11.LocalizationState framework input closed),
      CT11.Nodes.Routing.Contract framework input found) : CT11.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  decomposition := { certify := decomposition }
  admissibility := { decide := admission }
  localization := { certify := localized }
  routing := { route := route }

def ct10Plan : CT11.CorePlan framework input :=
  makePlan (fun _state => .refine {
    downstream := CT6CT10Fixtures.ct10Input, aligned := trivial })
    (fun _ => .toCT14 { downstream := CT6CT10Fixtures.ct14Input, aligned := trivial })
def ct1Plan : CT11.CorePlan framework input :=
  makePlan (fun state => .closed (admissible state))
    (fun _ => .toCT1 { downstream := CT1Toy.routingInput, aligned := trivial })
def ct7Plan : CT11.CorePlan framework input :=
  makePlan (fun state => .closed (admissible state))
    (fun _ => .toCT7 { downstream := CT6CT10Fixtures.ct7Input, aligned := trivial })
def ct14Plan : CT11.CorePlan framework input :=
  makePlan (fun state => .closed (admissible state))
    (fun _ => .toCT14 { downstream := CT6CT10Fixtures.ct14Input, aligned := trivial })

def port : CT11.Port framework input where accepts := fun _ => True
def handoff : CT11.HandoffPlan framework input port where accept := fun _ => trivial
def ct10Result := CT11.runTraced framework input ct10Plan port handoff
def ct1Result := CT11.runTraced framework input ct1Plan port handoff
def ct7Result := CT11.runTraced framework input ct7Plan port handoff
def ct14Result := CT11.runTraced framework input ct14Plan port handoff
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem ct1_terminal : ct1Result.terminal = .ct1 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct14_terminal : ct14Result.terminal = .ct14 := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .decompositionCertification, .admissibilityDecision,
      .ct10Terminal] := rfl
theorem ct1_trace : ct1Result.trace =
    [.entry, .scopeDecision, .decompositionCertification, .admissibilityDecision,
      .localizationCertification, .routingDecision, .ct1Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .decompositionCertification, .admissibilityDecision,
      .localizationCertification, .routingDecision, .ct7Terminal] := rfl
theorem ct14_trace : ct14Result.trace =
    [.entry, .scopeDecision, .decompositionCertification, .admissibilityDecision,
      .localizationCertification, .routingDecision, .ct14Terminal] := rfl

def scopeEntry : CT11.Interface.Framework :=
  { CT6CT10Fixtures.ct11Entry with ScopeReady := fun _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT11.Input scopeFramework where
  G := (); branch := (); deficit := (); decomposition := (); admissibility := (); localType := ()
def scopePlan : CT11.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun h => h⟩ }
  decomposition := { certify := fun s => False.elim s.ready }
  admissibility := { decide := fun s => False.elim s.scope.ready }
  localization := { certify := fun {decomposition} _ => False.elim decomposition.scope.ready }
  routing := { route := fun {decomposition} _ => False.elim decomposition.scope.ready }
def scopePort : CT11.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT11.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT11.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT11.OutcomeClaim ct1Result.outcome := by
  ct11 input using ct1Plan with port via handoff
example : ∃ result : CT11.ExecutionResult framework input port,
    CT11.OutcomeClaim result.outcome ∧ @CT11.Graph.ValidTrace framework input result.trace := by
  ct11_total input using ct1Plan with port via handoff

end StructuralExhaustion.Examples.CT11Toy
