import StructuralExhaustion.CT12.Automation
import StructuralExhaustion.Examples.CT4Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT12Toy
open StructuralExhaustion

def mkFramework (entry : CT12.Interface.Framework) : CT12.Framework where
  entry := entry
  ct4 := CT4Toy.framework
  ct13 := CT6CT10Fixtures.ct13Entry
  LoopInvariant := fun _ _ => True
  PeelCertified := fun _ _ => True
  StateRestored := fun _ current next => next < current
  CT4Aligned := fun _ _ => True
  CT13Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct12Entry
def input : CT12.Input framework := CT6CT10Fixtures.ct12Input

private def saturationPlan : CT12.Nodes.Saturation.Plan framework input where
  decide := fun {load} _state =>
    match load with
    | 0 => .close { closes := trivial }
    | n + 1 => .peel { positive := Nat.zero_lt_succ n }

private def peelPlan : CT12.Nodes.Peel.Plan framework input where
  certify := fun _ => ⟨trivial⟩

private def decreasePlan : CT12.Nodes.Decrease.Plan framework input where
  certify := fun restored => ⟨restored.restored⟩

private def basePlan (restoration : CT12.Nodes.Restoration.Plan framework input) :
    CT12.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  measure := { certify := fun _ => ⟨trivial⟩ }
  saturation := saturationPlan
  peel := peelPlan
  restoration := restoration
  decrease := decreasePlan

def c4Plan : CT12.CorePlan framework input := basePlan {
  decide := fun {load} {_state} {peelable} _peeled =>
    match load with
    | 0 => False.elim (Nat.not_lt_zero 0 peelable.positive)
    | n + 1 => .continue {
        nextState := ⟨trivial⟩
        restored := Nat.lt_succ_self n
      }
}
def ct4Plan : CT12.CorePlan framework input := basePlan {
  decide := fun _ => .toCT4 {
    downstream := CT4Toy.input
    aligned := trivial
  }
}
def ct13Plan : CT12.CorePlan framework input := basePlan {
  decide := fun _ => .toCT13 {
    downstream := CT6CT10Fixtures.ct13Input
    aligned := trivial
  }
}

def port : CT12.Port framework input where accepts := fun _ => True
def handoff : CT12.HandoffPlan framework input port where accept := fun _ => trivial
def c4Result := CT12.runTraced framework input c4Plan port handoff
def ct4Result := CT12.runTraced framework input ct4Plan port handoff
def ct13Result := CT12.runTraced framework input ct13Plan port handoff
theorem c4_terminal : c4Result.terminal = .c4 := by native_decide
theorem ct4_terminal : ct4Result.terminal = .ct4 := by native_decide
theorem ct13_terminal : ct13Result.terminal = .ct13 := by native_decide
theorem c4_trace : c4Result.trace =
    [.entry, .scopeDecision, .measureCertification, .saturationDecision,
      .peelCertification, .restorationDecision, .decreaseCertification,
      .saturationDecision, .c4Terminal] := by native_decide
theorem ct4_trace : ct4Result.trace =
    [.entry, .scopeDecision, .measureCertification, .saturationDecision,
      .peelCertification, .restorationDecision, .ct4Terminal] := by native_decide
theorem ct13_trace : ct13Result.trace =
    [.entry, .scopeDecision, .measureCertification, .saturationDecision,
      .peelCertification, .restorationDecision, .ct13Terminal] := by native_decide

def scopeEntry : CT12.Interface.Framework :=
  { CT6CT10Fixtures.ct12Entry with ScopeReady := fun _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT12.Input scopeFramework where
  G := (); branch := (); account := (); peelMove := (); load := 1
def scopePlan : CT12.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun h => h⟩ }
  measure := { certify := fun s => False.elim s.ready }
  saturation := {
    decide := fun _state => .close { closes := trivial }
  }
  peel := { certify := fun _peelable => ⟨trivial⟩ }
  restoration := {
    decide := fun _peeled => .toCT13 {
      downstream := CT6CT10Fixtures.ct13Input, aligned := trivial }
  }
  decrease := { certify := fun restored => ⟨restored.restored⟩ }
def scopePort : CT12.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT12.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT12.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT12.OutcomeClaim c4Result.outcome := by
  ct12 input using c4Plan with port via handoff
example : ∃ result : CT12.ExecutionResult framework input port,
    CT12.OutcomeClaim result.outcome ∧ @CT12.Graph.ValidTrace framework input result.trace := by
  ct12_total input using c4Plan with port via handoff

end StructuralExhaustion.Examples.CT12Toy
